import Inf.Util.Matrix
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import Inf.Util.Range

/-! # Gaussian elimination -/

namespace VecMatrix

theorem toMatrix_swap [Semiring R] (A : VecMatrix m n R) (i j : Fin m) :
    toMatrix (A.swap i j) = Matrix.swap R i j * A.toMatrix := by
  ext a b; simp [Vector.getElem_swap, Fin.val_inj]
  split_ifs <;> try simp [*]
  rw [Matrix.swap_mul_of_ne] <;> simp [*]

theorem toMatrix_transvectSub [CommRing R] (A : VecMatrix m n R) (i j : Fin m) (c : R) :
    (A.transvectSub i j c).toMatrix = Matrix.transvection i j (-c) * A.toMatrix := by
  ext a b; by_cases! h : a = i
  · simp [h, sub_eq_add_neg]
  simp [h, Fin.val_inj, h.symm]

/-- Find the first nonzero element in column `c` starting at row `r`. -/
@[inline]
def findNonzero [Zero R] [DecidableEq R] (A : VecMatrix m n R) (c : Fin n) (r : Fin m) :
    Option (Fin m × R) := do
  for i in r...* do
    let e := A[i][c]
    if e ≠ 0 then return (i, e)
  throw ()

/-- Perform Gaussian elimination on a linear equation `A * x = B` with square `A`, producing a pair
of matrices `A'` and `B'` with the same solution to `A' * x = B'` and `A'` upper triangular, or
`none` if `A` is degenerate. -/
@[inline]
def gauss [Zero R] [Div R] [Mul R] [Sub R] [DecidableEq R] (A : VecMatrix m m R)
    (B : VecMatrix m n R) : Option (VecMatrix m m R × VecMatrix m n R) := do
  let mut A := A
  let mut B := B
  for hi : i in *...m do
    let i : Fin m := ⟨i, hi⟩
    let (r, e) ← findNonzero A i i
    A := A.swap i r
    B := B.swap i r
    for r in i<...* do
      let d := A[r][i] / e
      A := A.transvectSub r i d
      B := B.transvectSub r i d
  return (A, B)

abbrev GaussInvariant [CommRing R] (A : VecMatrix m m R) (B : VecMatrix m n R)
    (A' : VecMatrix m m R) (B' : VecMatrix m n R) (i : ℕ) (_ : i ≤ m) : Prop :=
  A'.toMatrix.det ≠ 0 ∧ A'.toMatrix⁻¹ * B'.toMatrix = A.toMatrix⁻¹ * B.toMatrix ∧
  ∀ j (hj : j < i), A'[j][j] ≠ 0 ∧ ∀ r : Fin m, j < r → A'[r.val][j] = 0

set_option mvcgen.warning false in
open Std.Do in
/-- **Proof of correctness** of `gauss`. -/
theorem gauss_correct [Field K] [DecidableEq K] (A : VecMatrix m m K) (B : VecMatrix m n K)
    (hA : A.toMatrix.det ≠ 0) : ∃ A' B', gauss A B = some (A', B') ∧ GaussInvariant A B A' B' m le_rfl := by
  apply Option.of_wp_eq rfl fun x => ∃ A' B', x = some (A', B') ∧ GaussInvariant A B A' B' m le_rfl
  mvcgen [gauss, findNonzero] invariants
  | inv1 => ⇓⟨icur, A', B'⟩ =>
    ⌜GaussInvariant A B A' B' icur.pos (by convert icur.pos_le_length; simp)⌝
  | inv2 A' B' i _ => Invariant.withEarlyReturnNewDo (fun rcur _ => ⌜∀ j ∈ rcur.prefix, A'[j][i] = 0⌝)
      fun (r, e) _ => ⌜i ≤ r ∧ A'[r][i] = e ∧ e ≠ 0⌝
  | inv3 ip _ _ hi _ _ _ i _ _ _ _ _ A' B' => ⇓⟨rcur, A'', B''⟩ =>
    ⌜GaussInvariant A B A'' B'' ip.length (Nat.length_pref_le_rio hi)
    ∧ A''[i][i] = A'[i][i] ∧ ∀ r' ∈ rcur.prefix, A''[r'][i] = 0⌝
  with try grind
  · simp; constructor; swap; grind
    rename_i h _ _ _ _; exact Std.Rci.cur_mem h
  · expose_names
    have : Invertible (Matrix.transvection cur_1 i (-d)).det :=
      invertibleOfNonzero (by simp [(Std.Roi.cur_mem h_3).ne'])
    have this' := (Matrix.transvection cur_1 i (-d)).invertibleOfDetInvertible
    and_intros
    · simp [A_4, toMatrix_transvectSub, A_3, h_4, this.ne_zero]
    · simp [A_4, B_4, toMatrix_transvectSub, Matrix.mul_inv_rev, A_3, B_3,
        ← h_4.1.2.1, Matrix.mul_assoc]
    · intro j hj; simp [A_4, A_3]
      convert h_4.1.2.2 j hj using 3 with r hr
      · have : j < cur_1 := (hj.trans_eq (Nat.length_pref_rio h)).trans
          (by simpa [Std.Roi.mem_iff, i, Fin.lt_def] using Std.Roi.cur_mem h_3)
        simp [this.ne']
      · congr! 1; by_cases! hr' : cur_1 ≠ r
        · simp [hr', Fin.val_inj]
        subst cur_1; simp; right
        exact (h_4.1.2.2 j hj).2 i (hj.trans_eq (Nat.length_pref_rio h))
    · simp [A_4]; rw [getElem_transvectSub_ne]; exact h_4.2.1
      simpa [Fin.val_inj] using (Std.Roi.cur_mem h_3).ne'
    · simp; rintro r' (hr' | rfl)
      · convert h_4.2.2 r' hr'; simp [A_4, A_3]; apply getElem_transvectSub_ne
        simpa [Fin.val_inj] using Std.Roi.cur_ne_pref h_3 hr'
      · simp [h_2] at h_5; simp [A_4, d]; field_simp [h_5]
        simp [← h_5.2.1, sub_eq_zero, A_3, ← Fin.getElem_fin, h_4.2.1, A_2]; simp
  · expose_names; simp [A_2, A_1, B_2, B_1]; and_intros
    · simp [toMatrix_swap, Matrix.swap, h_1.1]; split <;> simp
    · simpa [toMatrix_swap, Matrix.mul_inv_rev, ← Matrix.GeneralLinearGroup.val_swap,
        Matrix.mul_assoc] using h_1.2.1
    · intro j hj
      have : j < i := hj.trans_eq (Nat.length_pref_rio h)
      have this' : j < a.1 := by simp [h_2] at h_3; exact this.trans_le h_3.1
      convert h_1.2.2 j hj using 2 with r
      · simp [this.ne, this'.ne]
      · congr! 2 with hr; simp [Vector.getElem_swap, Fin.val_inj]; split_ifs
        · subst r; simp [(h_1.2.2 j hj).2, this, this']
        · subst r; simp [(h_1.2.2 j hj).2, this', this]
        · rfl
  · expose_names; simp_all [GaussInvariant, A_3, B_3, le_iff_lt_or_eq]
    rintro j (hj | rfl); apply h_3.1.2.2 j hj
    simp [i, Std.Roi.mem_toList_iff_mem] at h_3
    simp [Nat.length_pref_rio h, h_3.2.1, A_2, i, h_4]; exact h_3.2.2
  pick_goal 4
  · exact Option.instWPMonad.{0}
  · expose_names; rcases h_1 with ⟨hA, hB, h'⟩; revert hA; simp; change A_1.toMatrix.det = 0
    apply Matrix.det_eq_zero_of_not_linearIndependent_cols
    apply mt fun h => h.linearIndepOn (Finset.Iic i)
    rw [← (LinearMap.funLeft K K (Fin.castLE i.isLt.le)).linearIndepOn_iff_of_injOn]
    · apply mt LinearIndependent.fintype_card_le_finrank; simp
    apply Set.LeftInvOn.injOn; swap
    · exact fun v j => if h : j < i then v ⟨j, h⟩ else 0
    · simp [Set.LeftInvOn]; apply Submodule.span_induction
      · simp [funext_iff]; intro v j hj hv r hr; rw [← hv]; symm
        rw [le_iff_eq_or_lt] at hj; rcases hj with rfl | hj
        · simp [h_2] at h_3; apply h_3; simpa [Std.Rci.mem_toList_iff_mem, Std.Rci.mem_iff]
        apply (h' j ?_).2 r (hj.trans_le hr); simp [Nat.length_pref_rio h]; exact hj
      · simp; rfl
      · rintro x y _ _ hx hy; nth_rw 2 [← hx, ← hy]; simp [funext_iff, ite_add_ite]
      · intro c v _ hv; nth_rw 2 [← hv]; simp [funext_iff]
  · simp_all; assumption

/-- Solve the linear equation `A * x = B` for upper triangular `A` via backwards substitution. -/
@[inline]
def backSubst [Div R] [Mul R] [Sub R] (A : VecMatrix m m R) (B : VecMatrix m n R) :
    VecMatrix m n R := go B m (Nat.le_refl m) where
  @[inline] go (B : VecMatrix m n R) : (i : Nat) → i ≤ m → VecMatrix m n R
  | 0,     _ => B
  | i + 1, h => Id.run do
    let mut B : VecMatrix m n R := B.modify i fun row => row.map (· / A[i][i])
    for hj : j in *...i do
      B := B.transvectSub ⟨j, by get_elem_tactic⟩ ⟨i, h⟩ A[j][i]
    go B i (Nat.le_of_succ_le h)

/-- Compute `A⁻¹ * B`. -/
def ldiv [Field K] [DecidableEq K] (A : VecMatrix m m K) (B : VecMatrix m n K)
    (hA : A.toMatrix.det ≠ 0) : VecMatrix m n K :=
  backSubst.uncurry <| (gauss A B).get (by have ⟨A', B', h⟩ := gauss_correct A B hA; simp [h])

/-- Compute `A⁻¹`. -/
def inv [Field K] [DecidableEq K] (A : VecMatrix m m K) (hA : A.toMatrix.det ≠ 0) :=
  ldiv A (1 : VecMatrix m m K) hA
