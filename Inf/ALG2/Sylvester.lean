import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped ComplexOrder

@[simp]
lemma Matrix.posDef_fin_one [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [NoZeroDivisors R] [Nontrivial R] {M : Matrix (Fin 1) (Fin 1) R} : M.PosDef ↔ 0 < M 0 0 := by
  convert posDef_diagonal_iff (d := ![M 0 0]) <;> simp [← Matrix.ext_iff]

/-- **Sylvester's criterion** for positive-definite matrices: a Hermitian matrix is
positive-definite iff all of its leading principal minors are positive. -/
theorem Matrix.posDef_sylvester [RCLike K] {A : Matrix (Fin n) (Fin n) K} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i : Fin n, 0 < (A.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).det := by
  use fun h i => (h.submatrix (Fin.castLE_injective _)).det_pos
  intro h; induction n
  case zero => simp [posDef_iff_dotProduct_mulVec, IsHermitian.ext_iff, funext_iff]
  rename_i n ih
  rw [PosSemidef.posDef_iff_det_ne_zero]; · simpa using (h (.last n)).ne'
  rw [← posSemidef_submatrix_equiv finSumFinEquiv]
  rw [← isHermitian_reindex_iff finSumFinEquiv.symm, reindex_apply, Equiv.symm_symm] at hA
  have hd := by simpa using h (Fin.last n)
  rw [← det_submatrix_equiv_self finSumFinEquiv] at hd
  rw [← Matrix.fromBlocks_toBlocks (A.submatrix _ _)] at ⊢ hA hd
  rw [isHermitian_fromBlocks_iff] at hA; rw [← hA.2.1] at ⊢ hd
  specialize ih hA.1 fun i => h i.castSucc; have := ih.isUnit.invertible
  rw [ih.fromBlocks₁₁]; rw [det_fromBlocks₁₁, mul_pos_iff_of_pos_left ih.det_pos] at hd
  apply PosDef.posSemidef; simpa using hd

theorem Matrix.posDef_sylvester_iff [RCLike K] {A : Matrix (Fin n) (Fin n) K} : A.PosDef ↔
    A.IsHermitian ∧ ∀ i : Fin n, 0 < (A.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).det :=
  ⟨fun h => ⟨h.isHermitian, (posDef_sylvester h.isHermitian).mp h⟩,
    fun h => (posDef_sylvester h.1).mpr h.2⟩

@[simp]
theorem Matrix.posDef_fin_two [RCLike K] {A : Matrix (Fin 2) (Fin 2) K} :
    A.PosDef ↔ A.IsHermitian ∧ 0 < A 0 0 ∧ A 0 1 * A 1 0 < A 0 0 * A 1 1 := by
  simp [posDef_sylvester_iff, det_fin_two]

@[simp]
lemma Fin.forall_fin_three {p : Fin 3 → Prop} : (∀ (i : Fin 3), p i) ↔ p 0 ∧ p 1 ∧ p 2 := by
  simp [Fin.forall_fin_succ]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem Matrix.posDef_fin_three [RCLike K] {A : Matrix (Fin 3) (Fin 3) K} :
    A.PosDef ↔ A.IsHermitian ∧ 0 < A 0 0 ∧ A 0 1 * A 1 0 < A 0 0 * A 1 1
    ∧ A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 + A 0 2 * A 1 1 * A 2 0
    < A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 := by
  simp [posDef_sylvester_iff, det_fin_two, det_fin_three]; grind
