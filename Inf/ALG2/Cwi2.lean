import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

open Real Matrix InnerProductSpace RealInnerProductSpace

namespace ALG2

alias Zad2_1a := inner_zero_right
alias Zad2_1b := inner_zero_left

alias ⟨Zad2_2, _⟩ := trace_conjTranspose_mul_self_eq_zero_iff

namespace Zad2_3

variable [Fintype n] [DecidableEq n] [RCLike K]

attribute [scoped instance] frobeniusNormedAddCommGroup frobeniusNormedSpace

/-- The standard inner product on real- or complex-valued matrices, given by
`⟪A, B⟫ = (Aᴴ * B).trace`. -/
noncomputable scoped instance innerProductSpace : InnerProductSpace K (Matrix n n K) where
  inner A B := (Aᴴ * B).trace
  conj_inner_symm A B := by trans (Bᴴ * A).conjTranspose.trace; simp [-conjTranspose_mul]; simp
  add_left A B C := by simp [add_mul]
  smul_left A B r := by simp
  norm_sq_eq_re_inner A := by
    rw [frobenius_norm_def, one_div, ← Nat.cast_ofNat, rpow_inv_natCast_pow (by positivity) two_ne_zero]
    simpa [trace, mul_apply, RCLike.norm_sq_eq_def] using Finset.sum_comm

@[simp]
lemma inner_def (A B : Matrix n n K) : ⟪A, B⟫_K = (Aᴴ * B).trace := rfl

@[simp]
lemma norm_def (A : Matrix n n K) : ‖A‖ = √(RCLike.re (Aᴴ * A).trace) := by simp [← inner_def]

end Zad2_3

open Zad2_3 in
theorem Zad2_4 : ‖!![(2 : ℝ), 1; 0, 2]‖ = 3 := by norm_num [trace, mul_apply, sqrt_eq_cases]

open MeasureTheory in
/-- A nonnegative `u` induces an inner product on `C(Set.Icc a b, ℝ)` given by
`⟪f, g⟫ = ∫ x, f x * g x * u x`. -/
@[implicit_reducible]
noncomputable def Zad2_5a {a b : ℝ} (u : C(Set.Icc a b, ℝ)) (hu : ∀ x, 0 ≤ u x) :
    PreInnerProductSpace.Core ℝ C(Set.Icc a b, ℝ) where
  inner f g := ∫ x : Set.Icc a b, f x * g x * u x ∂volume.comap Subtype.val
  conj_inner_symm f g := by simp [mul_comm]
  re_inner_nonneg f := by
    simp_rw [RCLike.re_to_real, ← sq]; apply integral_nonneg
    simp_rw [Pi.le_def, Pi.zero_apply]; bound
  add_left f₁ f₂ g := by
    have : IsFiniteMeasureOnCompacts (volume.comap Subtype.val : Measure (Set.Icc a b)) :=
      .comap' volume continuous_subtype_val (MeasurableEmbedding.subtype_coe measurableSet_Icc)
    simp [add_mul]; apply integral_add <;> rw [← integrableOn_univ]
      <;> exact ContinuousOn.integrableOn_compact isCompact_univ (by fun_prop)
  smul_left f g r := by simp [← integral_const_mul]; congr! 2; ring

open InnerProductGeometry in
theorem Zad2_6 : angle !₂[(1 : ℝ), 2, 3] !₂[3, -1, 2] = π / 3 := by
  simp [angle, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]; norm_num
  apply arccos_eq_of_eq_cos <;> bound

open Zad2_3 in
theorem Zad2_8 : (ℝ ∙ !![(4 : ℝ), 2; -2, 1]).starProjection !![-2, 1; 0, 2] =
    !![-(16 / 25), -(8 / 25); 8 / 25, -(4 / 25)] := by
  norm_num [Submodule.starProjection_singleton, trace, mul_apply]

theorem Zad2_9 [CommRing R] [NoZeroDivisors R] [Fintype n] [DecidableEq n] {A : Matrix n n R}
    (h : Aᵀ * A = 1) : A.det = 1 ∨ A.det = -1 := by
  apply_fun det at h; simp_all [← sq]
