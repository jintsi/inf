import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open Module LinearMap Polynomial

namespace ALG2

theorem Zad5_1a (a : ℝ[X]) : IsLinearMap ℝ fun p : ℝ[X] => ∫ t in -1..1, a.eval t * p.eval t where
  map_add p q := by simp [mul_add]; apply intervalIntegral.integral_add <;>
    apply Continuous.intervalIntegrable <;> fun_prop
  map_smul c p := by simp [mul_left_comm]

theorem Zad5_1c [Semiring R] (t : R) :
    IsLinearMap R fun p : R[X] => (derivative^[2] p).eval t + (derivative p).eval (t + 1) :=
  (leval t ∘ₗ derivative ^ 2 + leval (t + 1) ∘ₗ derivative).isLinear

/-- The linear form `F ![x, y, z] = x + 3 * y + 6 * z`. -/
def Zad5_2.F (R) [Semiring R] : Dual R (Fin 3 → R) where
  toFun x := x 0 + 3 * x 1 + 6 * x 2
  map_add' x y := by simp [mul_add]; ac_nf
  map_smul' c x := by simp [mul_add, (Commute.ofNat_left _ c).left_comm]

open Zad5_2 in
theorem Zad5_2b [CommSemiring R] : toMatrix (Pi.basisFun R (Fin 3)) (Basis.singleton (Fin 1) R) (F R)
    = !![1, 3, 6] := by ext i j; fin_cases j <;> simp [LinearMap.toMatrix_apply, F]

/-- Basis `![![1, 0, 0], ![1, 1, 0], ![1, 1, 1]]`. -/
noncomputable def Zad5_2c.basis (R) [DivisionRing R] : Basis (Fin 3) R (Fin 3 → R) := by
  apply basisOfLinearIndependentOfCardEqFinrank' ![![1, 0, 0], ![1, 1, 0], ![1, 1, 1]]
  · simp [linearIndependent_finSucc, Submodule.mem_span_singleton, Submodule.mem_span_pair]
  · simp

@[simp]
theorem Zad5_2c.basis_apply [DivisionRing R] :
    basis R i = ![![1, 0, 0], ![1, 1, 0], ![1, 1, 1]] i := by simp [basis]

open Zad5_2 Zad5_2c in
theorem Zad5_2c [Field K] : toMatrix (basis K) (Basis.singleton (Fin 1) K) (F K)
    = !![1, 4, 10] := by ext i j; fin_cases j <;> simp [LinearMap.toMatrix_apply, F] <;> norm_num

/-- `⟪x, y⟫ = x 0 * y 0 + 2 * x 1 * y 1 + 3 * x 2 * x 2 + x 0 * y 1 + x 1 * y 0`. -/
def Zad5_2d.inner (R) [Add R] [Mul R] [NatCast R] (x y : Fin 3 → R) :=
  x 0 * y 0 + 2 * x 1 * y 1 + 3 * x 2 * y 2 + x 0 * y 1 + x 1 * y 0

open Zad5_2 Zad5_2d in
theorem Zad5_2d [Ring R] : F R = inner R ![-1, 2, 2] := by
  ext x; simp [F, Zad5_2d.inner]; grind

open Matrix in
theorem Zad5_3 [Field K] [LinearOrder K] [AddLeftMono K] [PosMulMono K] [Fintype m] [Fintype n]
    (f : Dual K (Matrix m n K)) : ∃ A, ∀ x, f x = (A * x).trace := by
  let B : LinearMap.BilinForm K (Matrix m n K) := mk₂ K (fun a b => trace (aᵀ * b))
    (by simp [Matrix.add_mul]) (by simp) (by simp [Matrix.mul_add]) (by simp)
  have hB : B.Nondegenerate := by
    apply BilinForm.Nondegenerate.ofSeparatingLeft; intro a; contrapose!; intro ha
    use a; simp [B, trace, mul_apply, ← sq]
    rw [Fintype.sum_eq_zero_iff_of_nonneg (by simp [Pi.le_def, Fintype.sum_nonneg, sq_nonneg])]
    simp [funext_iff, Fintype.sum_eq_zero_iff_of_nonneg, Pi.le_def, sq_nonneg]
    rw [exists_comm]; simpa [← Matrix.ext_iff] using ha
  use ((B.toDual hB).symm f)ᵀ, fun x => (BilinForm.apply_toDual_symm_apply (B := B) f x).symm

theorem Zad5_4a [CommSemiring R] : Nat.factorial i.val • ⇑((degreeLT.basis R n).dualBasis i)
    = fun p => eval 0 (derivative^[i.val] p.val) := by
  ext p; simp [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, Nat.descFactorial_self]

/-- The linear form `F p = ∫ x in 0..1, eval x p` on `ℝ[X]_3`. -/
noncomputable def Zad5_4.F : Dual ℝ ℝ[X]_3 where
  toFun p := ∫ x in 0..1, eval x p
  map_add' p q := by
    simp; rw [intervalIntegral.integral_add] <;> (apply Continuous.intervalIntegrable; fun_prop)
  map_smul' c p := by simp

open Zad5_4 in
theorem Zad5_4b : ⇑((degreeLT.basis ℝ 3).dualBasis.repr F) = ![1, 2⁻¹, 3⁻¹] := by
  ext i; simp [F]; fin_cases i <;> norm_num

/-- Basis `B = ![!![1, 0; 0, 0], !![1, 1; 0, 0], !![1, 1; 1, 0], !![1, 1; 1, 1]]` -/
noncomputable def Zad5_5.B : Basis (Fin 4) ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  basisOfTopLeSpanOfCardEqFinrank ![!![1, 0; 0, 0], !![1, 1; 0, 0], !![1, 1; 1, 0], !![1, 1; 1, 1]]
    (by
      simp [Submodule.eq_top_iff', Submodule.mem_span_insert, Submodule.mem_span_singleton]
      intro A; simp [← Matrix.ext_iff]; use! A 1 0 - A 1 1, A 0 1 - A 1 0, A 0 0 - A 0 1 <;> ring)
    (by simp [finrank_matrix])

open Zad5_5 in
theorem Zad5_5 : B.dualBasis i x =
    (![!![1, 0; -1, 0], !![0, -1; 1, 0], !![0, 1; 0, -1], !![0, 0; 0, 1]] i * x).trace := by
  simp; apply Basis.repr_apply_eq _ _ (by simp [mul_add, Pi.add_def]) (by simp [Pi.smul_def])
  simp [Fin.forall_fin_succ, B, funext_iff, Matrix.trace]

theorem Zad5_6 [CommSemiring R] [AddCommGroup M] [Module R M] [DecidableEq ι] [Fintype ι]
    (B : Basis ι R M) [DecidableEq ι'] [Fintype ι'] (C : Basis ι' R M)
    : (C.dualBasis.toMatrix B.dualBasis).transpose * C.toMatrix B = 1 := by
  simp [← toMatrix_id_eq_basis_toMatrix, -Basis.coe_dualBasis, ← dualMap_id, dualMap_def,
    ← LinearMap.toMatrix_comp, toMatrix_id]

theorem Zad5_D1 [CommSemiring R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    (B₁ : Basis (Fin 3) R M₁) (B₂ : Basis (Fin 2) R M₂) :
    toMatrix B₂.dualBasis B₁.dualBasis (Matrix.toLin B₁ B₂ !![1, 2, 3; 5, 0, 1]).dualMap
    = !![1, 5; 2, 0; 3, 1] := by simp [dualMap]; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Zad5_D5 [Field K] [AddCommGroup V] [Module K V] {f g : Dual K V} (h : f.ker = g.ker) :
    g ∈ K ∙ f := by
  convert mem_span_of_iInf_ker_le_ker (L := ![f]) (K := g) (by simp [h])
  simp
