import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace ALG1.Cwi7

open Submodule

theorem Zad1a : Module.finrank ℂ (ℂ × ℂ) = 2 := by simp

theorem Zad1b : Module.finrank ℝ (ℂ × ℂ) = 4 := by simp

theorem Zad2a : ¬∀ v : ℝ, v ∈ span ℚ {1, √2} := by
  simp [mem_span_pair, Rat.smul_def]
  exists √3
  intro a b
  by_cases! hb : b = 0
  · subst b; simp
    refine (Irrational.ne_rat ?_ _).symm
    exact Nat.prime_three.irrational_sqrt
  apply_fun (· - b * √2); simp
  apply_fun (· ^ 2); simp [sub_sq, mul_pow]
  rw [← sub_eq_iff_eq_add]; ac_nf; simp [← mul_assoc]
  rw [← Real.sqrt_mul] <;> norm_num
  norm_cast; refine (Irrational.ne_rat ?_ _).symm
  have h : Irrational √6 := by rw [irrational_sqrt_ofNat_iff]; norm_num
  exact ((h.mul_natCast two_ne_zero).mul_ratCast hb).natCast_sub 3

theorem Zad2b (n : ℕ) : LinearIndependent ℚ fun (i : Fin n) => Real.log (Nat.nth Nat.Prime i) := by
  induction n; · simp
  rename_i n ih
  simp [linearIndependent_finSucc', Fin.init_def, ih, mem_span_range_iff_exists_fun, Rat.smul_def]
  intro x
  let den := Finset.univ.lcm fun i => (x i).den
  have h : ∀ i, (x i).den ∣ den := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  apply_fun Real.exp ∘ (↑den * ·); simp [Finset.mul_sum, Real.exp_sum, ← Real.log_pow]
  rw [Real.exp_log]; swap; simp [pow_pos, Nat.Prime.pos]
  rw [Fintype.prod_congr (g := fun i => (Nat.nth Nat.Prime i.val : ℝ) ^ ((x i).num * den / (x i).den))]
  case h =>
    intro i
    rw [← Real.exp_log (x := _ ^ _), Real.log_zpow, ← mul_assoc]; congr; norm_cast
    rw [Int.cast_div, mul_comm (G := ℤ)]
    · simp [mul_div_assoc, Rat.num_div_den]
    · grw [h]; simp
    · simp
    · apply zpow_pos; simp [Nat.Prime.pos]
  rw [← Finset.prod_filter_mul_prod_filter_not (p := fun i => 0 ≤ (x i).num)]; simp_rw [not_le]
  nth_rw 1 [Finset.prod_congr (g := fun i => (Nat.nth Nat.Prime i.val : ℝ) ^
    ((x i).num.toNat * den / (x i).den)) rfl]; swap
  · simp; intro i hi; rw [← zpow_natCast]; push_cast; congr; simpa
  nth_rw 2 [Finset.prod_congr (g := fun i => ((Nat.nth Nat.Prime i.val : ℝ) ^
    ((-(x i).num).toNat * den / (x i).den))⁻¹) rfl]; swap
  · simp [-Rat.num_neg]; intro i hi
    rw [← zpow_natCast, ← zpow_neg]; congr
    push_cast; rw [Int.natCast_toNat_eq_self.mpr (by omega)]; simp
    rw [Int.neg_ediv_of_dvd]; simp
    grw [h]; simp
  simp [← div_eq_mul_inv]; norm_cast
  nth_rw 1 [← Rat.cast_natCast]; nth_rw 2 [← Rat.cast_natCast]; nth_rw 3 [← Rat.cast_natCast]
  norm_cast; rw [div_eq_iff, mul_comm, ← div_eq_iff]
  apply_fun Rat.den
  rw [Rat.den_natCast, Ne, Rat.den_div_natCast_eq_one_iff, Nat.Prime.pow_dvd_iff_le_factorization,
    Nat.factorization_prod]
  all_goals simp [Nat.Prime.ne_zero, Finset.prod_ne_zero_iff]
  rw [Finset.sum_eq_zero, ← Nat.ne_zero_iff_zero_lt, Finset.lcm_ne_zero_iff]; simp
  intro i hi; apply Finsupp.single_eq_of_ne
  exact (Nat.nth_injective Nat.infinite_setOfPred_prime).ne i.isLt.ne'

/-- Symmetric matrices form a submodule. -/
def _root_.SymmMatrix (n : Type*) (R : Type*) [Semiring R] : Submodule R (Matrix n n R) where
  carrier := Set.ofPred Matrix.IsSymm
  add_mem' := Matrix.IsSymm.add
  zero_mem' := Matrix.isSymm_zero
  smul_mem' := fun c _ h => Matrix.IsSymm.smul h c

/-- Skew-symmetric matrices form a submodule. -/
def _root_.SkewSymmMatrix (n : Type*) (R : Type*) [Ring R] : Submodule R (Matrix n n R) where
  carrier := {A | A.transpose = -A}
  add_mem' := fun ha hb => (Matrix.transpose_add _ _).trans (ha ▸ hb ▸ (neg_add _ _).symm)
  zero_mem' := Matrix.transpose_zero.trans neg_zero.symm
  smul_mem' := fun c _ h => (Matrix.transpose_smul c _).trans (h ▸ smul_neg c _)

/-- Basis for `SymmMatrix`. -/
noncomputable def _root_.SymmMatrix.basis (n : Type*) [Finite n] (R : Type*) [Semiring R] :
    Module.Basis (Sym2 n) R (SymmMatrix n R) :=
  Module.Basis.ofEquivFun {
    toFun M := Sym2.lift ⟨M.val, M.prop.transpose.apply⟩
    map_add' := by simp [funext_iff, Sym2.forall]
    map_smul' := by simp [funext_iff, Sym2.forall]
    invFun c := ⟨.of fun i j => c s(i, j), by simp [SymmMatrix, Matrix.IsSymm.ext_iff, Sym2.eq_swap]⟩
    left_inv M := by ext; simp
    right_inv c := by simp [funext_iff, Sym2.forall]
  }

/-- Basis for `SkewSymmMatrix`. -/
noncomputable def _root_.SkewSymmMatrix.basis (n : Type*) [Fintype n] [LinearOrder n] (R : Type*) [Ring R]
    [IsAddTorsionFree R] : Module.Basis (Sym2.diagSetᶜ : Set (Sym2 n)) R (SkewSymmMatrix n R) :=
  Module.Basis.ofEquivFun {
    toFun M s := M.val s.val.sup s.val.inf
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun c := ⟨.of fun i j => if h : j < i then c ⟨s(i, j), by simp [h.ne']⟩ else if h : i < j
        then -c ⟨s(j, i), by simp [h.ne']⟩ else 0, by
      ext i j; rcases lt_trichotomy i j with h | h | h
      · simp [h, h.asymm]
      · simp [h.not_lt, h.not_gt]
      · simp [h, h.asymm]⟩
    left_inv := fun ⟨M, h⟩ => by
      simp; ext i j; simp; split; simp_all [le_of_lt]; split
      · rw [← Matrix.neg_apply, ← h, Matrix.transpose_apply]; simp_all
      · symm; rw [← _root_.neg_eq_self, ← Matrix.neg_apply, ← h, Matrix.transpose_apply]
        congr <;> order
    right_inv := fun c => by
      simp [funext_iff, Sym2.forall]; intro x y h; simp [eq_comm, h]; congr 2; simp [le_total]
  }

theorem Zad3a_symm (n : Type*) [Fintype n] (R : Type*) [Semiring R] [StrongRankCondition R] :
    Module.finrank R (SymmMatrix n R) = (Fintype.card n + 1).choose 2 := by
  rw [Module.finrank_eq_card_basis (SymmMatrix.basis n R), Sym2.card]

theorem Zad3a_skewSymm (n : Type*) [Fintype n] [LinearOrder n] (R : Type*) [Ring R]
    [IsAddTorsionFree R] [StrongRankCondition R] :
    Module.finrank R (SkewSymmMatrix n R) = (Fintype.card n).choose 2 := by
  rw [Module.finrank_eq_card_basis (SkewSymmMatrix.basis n R), Sym2.card_diagSet_compl]

instance Zad3b (R : Type*) [Field R] [CharZero R] [DecidableEq R] (n : ℕ) :
    DirectSum.Decomposition ![SymmMatrix (Fin n) R, SkewSymmMatrix (Fin n) R] := by
  constructor
  case decompose' =>
    intro m; apply DFinsupp.equivFunOnFintype.invFun; intro k; constructor
    case val => exact ![(2⁻¹ : R) • (m + m.transpose), (2⁻¹ : R) • (m - m.transpose)] k
    case property =>
      fin_cases k <;> (dsimp; apply smul_mem; ext i j; simp [add_comm])
  case left_inv =>
    intro m; ext i j; simp [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.equivFunOnFintype]; ring
  case right_inv =>
    intro ds; ext k i j; fin_cases k <;>
      (simp [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.equivFunOnFintype]; field_simp)
    · nth_rw 2 [← (ds 0).property, ← Matrix.transpose_apply (ds 1).val]; rw [(ds 1).property]
      simp; ring
    · rw [sub_eq_add_neg, neg_add]; nth_rw 2 [← (ds 0).property, ← Matrix.neg_apply]
      rw [← (ds 1).property]; simp; ring

theorem Zad3c : (fun k => (DirectSum.decompose ![SymmMatrix (Fin 2) ℚ, SkewSymmMatrix (Fin 2) ℚ]
    !![3, 4; 5, -2] k).val) = ![!![3, 9 / 2; 9 / 2, -2], !![0, -(1 / 2); 1 / 2, 0]] := by
  ext k i j
  simp [DirectSum.decompose, DirectSum.Decomposition.decompose', DFinsupp.equivFunOnFintype,
    Pi.smul_def]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The subspace of vectors in `Fin n → ZMod 2` with an even number of 1s (or alternatively, whose
coordinates sum to 0 mod 2). -/
def Zad4.A (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | Finset.univ.sum v = 0}
  add_mem' := fun ha hb => Finset.sum_add_distrib.trans (ha ▸ hb ▸ add_zero _)
  zero_mem' := Finset.sum_const_zero
  smul_mem' := by intro c _ h; simp [← Finset.mul_sum]; right; exact h

/-- The basis given by vectors `![1, 0, 0, ..., 1, ..., 0]`. -/
noncomputable def Zad4.basis (n : ℕ) : Module.Basis (Fin n) (ZMod 2) (A (n + 1)) :=
  Module.Basis.ofEquivFun {
    toFun := fun ⟨v, h⟩ i => v i.succ
    map_add' := fun ⟨a, ha⟩ ⟨b, hb⟩ => rfl
    map_smul' := fun r ⟨v, h⟩ => rfl
    invFun c := ⟨Fin.cons (Finset.univ.sum c) c, by simp [A]; grind⟩
    left_inv := fun ⟨v, h⟩ => by
      simp; ext i; cases i using Fin.cases
      case succ i => simp
      case zero => simp; rw [← add_right_inj (v 0), ← Fin.sum_univ_succ, h]; grind
  }

theorem Zad4.rank (n : ℕ) : Module.finrank (ZMod 2) (A (n + 1)) = n := by
  simp [Module.finrank_eq_nat_card_basis (basis n)]

/-- Solution set of equations:
```lean
x 0 + x 1 - 2 * x 2 + x 3 = 0
x 0 + 2 * x 1 - 3 * x 2 = 0
``` -/
def Zad5a.V1 : Submodule ℚ (Fin 4 → ℚ) := by
  apply ofLinearComb {x | x 0 + x 1 - 2 * x 2 + x 3 = 0 ∧ x 0 + 2 * x 1 - 3 * x 2 = 0}
  · exists 0; simp
  · simp; grind

/-- Solution set of equations:
```lean
x 0 - 3 * x 1 + x 2 - x 3 = 0
2 * x 0 + 3 * x 1 - 5 * x 2 + x 3 = 0
``` -/
def Zad5a.V2 : Submodule ℚ (Fin 4 → ℚ) := by
  apply ofLinearComb
    {x : Fin 4 → ℚ | x 0 - 3 * x 1 + x 2 - x 3 = 0 ∧ 2 * x 0 + 3 * x 1 - 5 * x 2 + x 3 = 0}
  · exists 0; simp
  · simp; grind

/-- `![1, 1, 1, 0]` and `![0, 3, 2, 1]` are a basis for V1. -/
noncomputable def Zad5a.basis_v1 : Module.Basis (Fin 2) ℚ V1 := by
  apply Module.Basis.mk (v := ![⟨![1, 1, 1, 0], by simp [V1, ofLinearComb]; norm_num⟩,
    ⟨![0, 3, 2, 1], by simp [V1, ofLinearComb]; norm_num⟩])
  · simp [LinearIndependent.pair_iff']
  · simp [eq_top_iff', mem_span_pair]
    simp [V1, ofLinearComb]
    intro x h1 h2; exists x 3, x 0; ext i; fin_cases i <;> simp <;> grind

set_option backward.isDefEq.respectTransparency false in
/-- `![0, 1, 0, -3]` and `![1, 0, 3 / 4, 7 / 4]` are a basis for V2. -/
noncomputable def Zad5a.basis_v2 : Module.Basis (Fin 2) ℚ V2 := by
  apply Module.Basis.mk (v := ![⟨![0, 1, 0, -3], by simp [V2, ofLinearComb]⟩,
    ⟨![1, 0, 3 / 4, 7 / 4], by simp [V2, ofLinearComb]; norm_num⟩])
  · simp [LinearIndependent.pair_iff']
  · simp [eq_top_iff', mem_span_pair]
    simp [V2, ofLinearComb]
    intro x h1 h2; exists x 0, x 1; ext i; fin_cases i <;> simp <;> grind

/-- `![1, 1, 1, 0]`, `![0, 1, 1, 2]`, and `![0, 0, 1, 5]` are a basis V1 + V2. -/
noncomputable def Zad5a.basis_sum : Module.Basis (Fin 3) ℚ (V1 + V2) := by
  apply Module.Basis.mk
  case v =>
    refine ![⟨![1, 1, 1, 0], ?_⟩, ⟨![0, 1, 1, 2], ?_⟩, ⟨![0, 0, 1, 5], ?_⟩] <;>
      simp [mem_sup, V1, V2, ofLinearComb]
    · exists ![1, 1, 1, 0]; simp; norm_num; exists 0; simp
    · exists ![0, 3 / 2, 1, 1 / 2]; simp; norm_num; exists ![0, -1 / 2, 0, 3 / 2]; simp; norm_num
    · exists ![0, 3 / 2, 1, 1 / 2]; simp; norm_num; exists ![0, -3 / 2, 0, 9 / 2]; simp; norm_num
  · simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  · simp [eq_top_iff', mem_span_triple, mem_sup]
    simp [V1, V2, ofLinearComb]
    intro v x h1 h2 y h3 h4 h; exists v 2 - v 1, v 1 - v 0, v 0; subst h
    ext i; fin_cases i <;> simp; grind

/-- `![8, 5, 6, -1]` spans `V1 ⊓ V2`. -/
noncomputable def Zad5a.basis_inf : Module.Basis (Fin 1) ℚ ↥(V1 ⊓ V2) := by
  apply Module.Basis.mk (v := ![⟨![8, 5, 6, -1], by simp [V1, V2, ofLinearComb]; norm_num⟩])
  · simp
  · simp [eq_top_iff', mem_span_singleton]
    simp [V1, V2, ofLinearComb]
    intro v h1 h2 h3 h4; exists -v 3; ext i; fin_cases i <;> simp <;> grind

abbrev Zad5b.V1 := span ℚ {!![(2 : ℚ), 1; 0, 2], !![-3, 4; 0, -3]}

abbrev Zad5b.V2 := span ℚ {!![(0 : ℚ), 1; 1, 1], !![-1, 2; 2, 1], !![2, 1; 1, 3]}

/-- `!![2, 1; 0, 2]` and `!![-3, 4; 0, -3]` are a basis for V1. -/
noncomputable def Zad5b.basis_v1 : Module.Basis (Fin 2) ℚ V1 := by
  let v := ![!![(2 : ℚ), 1; 0, 2], !![-3, 4; 0, -3]]
  convert Module.Basis.span (v := v) ?_ <;> simp [v, Set.pair_comm]
  rw [LinearIndependent.pair_iff']
  · norm_num +contextual
  · apply Function.ne_iff.mpr; exists 0

/-- `!![0, 1; 1, 1]` and `!![1, 0; 0, 1]` are a basis for V2. -/
noncomputable def Zad5b.basis_v2 : Module.Basis (Fin 2) ℚ V2 := by
  apply Module.Basis.mk
  case v =>
    refine ![⟨!![0, 1; 1, 1], ?_⟩, ⟨!![1, 0; 0, 1], ?_⟩] <;> simp [V2, mem_span_triple]
    · exists 1, 0, 0; simp
    · exists 2, -1, 0; norm_num
  · simp [LinearIndependent.pair_iff]
    rw [show 0 = !![(0 : ℚ), 0; 0, 0] from (Matrix.etaExpand_eq _).symm]; simp
  · simp [eq_top_iff', mem_span_pair, V2, mem_span_triple]
    intro m x y z h; exists m 0 0, m 0 1; subst h; simp; ring

/-- `!![1, 1; 0, 1]`, `!![0, 1; 1, 1]`, and `!![1, 0; 0, 1]` are a basis for V1 + V2. -/
noncomputable def Zad5b.basis_sum : Module.Basis (Fin 3) ℚ (V1 + V2) := by
  let v : Fin 3 → Matrix _ _ ℚ := ![!![1, 1; 0, 1], !![0, 1; 1, 1], !![1, 0; 0, 1]]
  have : V1 + V2 = span ℚ (Set.range v) := by
    ext m; simp [mem_sup, v, V1, V2, mem_span_pair, mem_span_triple]
    constructor
    · intro ⟨a, b, c, d, e, h⟩; exists m 1 1 - m 0 1, m 1 0, m 0 1 - m 1 0
      subst h; simp; ring_nf; simp
    · rintro ⟨a, b, c, rfl⟩; exists 7 / 11 * c, c / 11, b, -a / 5, 2 / 5 * a; simp; ring_nf; simp
  rw [this]; apply Module.Basis.span
  simp [v, linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  apply_fun fun m => m 0 0; simp

/-- `!![1, 0; 0, 1]` spans `V1 ⊓ V2`. -/
noncomputable def Zad5b.basis_inf : Module.Basis (Fin 1) ℚ ↥(V1 ⊓ V2) := by
  apply Module.Basis.mk
  case v =>
    refine ![⟨!![1, 0; 0, 1], ?_⟩]
    simpa [V1, V2, mem_span_pair, mem_span_triple] using
      ⟨⟨4 / 11, -1 / 11, by norm_num⟩, 2, -1, 0, by norm_num⟩
  · simp [Matrix.eta_fin_two 0]
  · simp [eq_top_iff', mem_span_singleton,
      V1, V2, mem_span_pair, mem_span_triple]
    intro m a b h1 c d e h2; exists m 0 0
    rw [m.eta_fin_two] at *; simp at *; grind

theorem Zad6 {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M] {s t : Submodule R M}
    (h : s + t = ⊤) : s ⊓ t = ⊥ ↔ ∀ v : M, ∃! v' : s × t, v = v'.1 + v'.2 := by
  simp at h; constructor
  · convert fun hb => existsUnique_add_of_isCompl_prod (IsCompl.of_eq hb h) using 4
    simp [Eq.comm]
  · simp [← disjoint_iff, disjoint_def]; intro h x hs ht
    replace h := (h x).unique (y₁ := ⟨⟨x, hs⟩, 0⟩) (y₂ := ⟨0, x, ht⟩); simp at h; tauto

theorem Zad7.directSum_V1_V2 : DirectSum.IsInternal (M := ℚ × ℚ) ![ℚ ∙ (1, 0), ℚ ∙ (0, 1)] := by
  rw [DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (by ext i; fin_cases i <;> simp)]
  simp [isCompl_iff, disjoint_span_singleton', codisjoint_iff_exists_add_eq, mem_span_singleton]

theorem Zad7.directSum_V1_V3 : DirectSum.IsInternal (M := ℚ × ℚ) ![ℚ ∙ (1, 0), ℚ ∙ (1, 1)] := by
  rw [DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (by ext i; fin_cases i <;> simp)]
  simp [isCompl_iff, disjoint_span_singleton', codisjoint_iff_exists_add_eq, mem_span_singleton]
  intro a b; exists a - b; simp

theorem Zad7.V2_ne_V3 : ℚ ∙ ((0, 1) : ℚ × ℚ) ≠ ℚ ∙ (1, 1) := by
  simp [Submodule.ext_iff, mem_span_singleton]; exists 1, 1

/-- The submodule `{(x, y, z) | z = x + y}`. -/
def Zad8.A : Submodule ℚ (ℚ × ℚ × ℚ) := by
  apply ofLinearComb {(x, y, z) | z = x + y}
  · exists 0; simp
  · simp; grind

/-- The submodule `{(x, y, z) | x = y = z}`. -/
def Zad8.B : Submodule ℚ (ℚ × ℚ × ℚ) := by
  apply ofLinearComb {(x, x, x) | (x : ℚ)}
  · exists 0; simp
  · simp

theorem Zad8.directSum : DirectSum.IsInternal ![A, B] := by
  rw [DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (by simp [Set.ext_iff])]
  simp [isCompl_iff, disjoint_def, codisjoint_iff_exists_add_eq, A, B, ofLinearComb]
  intro a b c; exists c - b, c - a, a + b - c; simp; ring

def Zad9.A : Submodule ℚ (ℚ × ℚ × ℚ × ℚ) := span ℚ {(2, 3, 11, 5), (1, 1, 5, 2), (0, 1, 1, 1)}
--(0, 1, 1, 1) and (1, 0, 4, 1)
def Zad9.B : Submodule ℚ (ℚ × ℚ × ℚ × ℚ) := span ℚ {(2, 1, 3, 2), (1, 4, 3, 4), (5, -1, 6, 2)}
--(1, 4, 3, 4) and (1, -3, 0, -2) or (0, 7, 3, 6)

set_option backward.isDefEq.respectTransparency false
theorem Zad9.directSum : DirectSum.IsInternal ![A, B] := by
  rw [DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (by simp [Set.ext_iff]), isCompl_iff_disjoint]
  · simp [disjoint_def, A, B, mem_span_triple]; grind only
  simp [A, B]; grw [← LinearIndependent.fintype_card_le_finrank (b := ![
      ⟨(1, 1, 5, 2), mem_span_of_mem (by simp)⟩, ⟨(0, 1, 1, 1), mem_span_of_mem (by simp)⟩]),
    ← LinearIndependent.fintype_card_le_finrank (b := ![
      ⟨(2, 1, 3, 2), mem_span_of_mem (by simp)⟩, ⟨(1, 4, 3, 4), mem_span_of_mem (by simp)⟩])]
  · simp
  · simp [linearIndependent_fin2]
  · simp [linearIndependent_fin2]

theorem ZadD1 {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
    Module.finrank K (s + t) = Module.finrank K s + Module.finrank K t - Module.finrank K ↥(s ⊓ t) := by
  rw [← finrank_sup_add_finrank_inf_eq s t, add_tsub_cancel_right, Submodule.add_eq_sup]
