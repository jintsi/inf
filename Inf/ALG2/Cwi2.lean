import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Inf.ALG1.Cwi7

open Real Matrix InnerProductSpace RealInnerProductSpace

namespace ALG2.Cwi2

alias Zad1a := inner_zero_right
alias Zad1b := inner_zero_left

theorem Zad2 [Semiring R] [LinearOrder R] [ExistsAddOfLE R] [AddLeftMono R] [PosMulMono R]
    [NoZeroDivisors R] [Fintype n] {A : Matrix n n R} : (Aᵀ * A).trace = 0 ↔ A = 0 where
  mpr h := by simp [h]
  mp h := by
    simp [trace, mul_apply] at h; ext i j
    rw [Fintype.sum_eq_zero_iff_of_nonneg, funext_iff] at h; swap
    · intro j; apply Fintype.sum_nonneg; intro i; apply mul_self_nonneg
    specialize h j; rw [Pi.zero_apply, Fintype.sum_eq_zero_iff_of_nonneg, funext_iff] at h; swap
    · intro i; apply mul_self_nonneg
    exact mul_self_eq_zero.mp (h i)

namespace Zad3

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

end Zad3

open scoped Zad3 in
theorem Zad4 : ‖!![(2 : ℝ), 1; 0, 2]‖ = 3 := by norm_num [trace, mul_apply, sqrt_eq_cases]

open MeasureTheory in
attribute [local instance] Measure.Subtype.measureSpace in
instance _root_.isFiniteMeasureOnCompactsIccVolume {a b : α} [Preorder α] [TopologicalSpace α]
    [OrderClosedTopology α] [MeasureSpace α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts (volume : Measure α)] :
    IsFiniteMeasureOnCompacts (volume : Measure (Set.Icc a b)) :=
  .comap' volume continuous_subtype_val (MeasurableEmbedding.subtype_coe measurableSet_Icc)

open MeasureTheory in
attribute [local instance] Measure.Subtype.measureSpace in
/-- A nonnegative `u` induces an inner product on `C(Set.Icc a b, ℝ)` given by
`⟪f, g⟫ = ∫ x, f x * g x * u x`. -/
@[implicit_reducible]
noncomputable def Zad5a {a b : ℝ} (u : C(Set.Icc a b, ℝ)) (hu : ∀ x, 0 ≤ u x) :
    PreInnerProductSpace.Core ℝ C(Set.Icc a b, ℝ) where
  inner f g := ∫ x : Set.Icc a b, f x * g x * u x
  conj_inner_symm f g := by simp [mul_comm]
  re_inner_nonneg f := by
    simp_rw [RCLike.re_to_real, ← sq]; apply integral_nonneg
    simp_rw [Pi.le_def, Pi.zero_apply]; bound
  add_left f₁ f₂ g := by simp [add_mul]; apply integral_add <;> rw [← integrableOn_univ]
      <;> exact ContinuousOn.integrableOn_compact isCompact_univ (by fun_prop)
  smul_left f g r := by simp [← integral_const_mul]; congr! 2; ring

open MeasureTheory in
attribute [local instance] Measure.Subtype.measureSpace in
/-- For a positive `u`, the induced inner product on `C(Set.Icc a b, ℝ)` is positive-definite. -/
@[implicit_reducible]
noncomputable def Zad5b {a b : ℝ} (hab : a < b) (u : C(Set.Icc a b, ℝ)) (hu : ∀ x, 0 < u x) :
    InnerProductSpace.Core ℝ C(Set.Icc a b, ℝ) where
  toCore := Zad5a u (fun x => (hu x).le)
  definite f := by
    unfold inner Zad5a; dsimp; contrapose!
    simp [ContinuousMap.ext_iff, -Set.mem_Icc]; intro c hc hf
    apply ne_of_gt; calc ∫ x, (f * f * u) x
    _ = ∫ x : Set.Icc a b, Set.IccExtend hab.le (f * f * u) x := by simp
    _ = ∫ x in Set.Icc a b, _ := integral_subtype measurableSet_Icc _
    _ = ∫ x in Set.Ioc a b, _ := integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, _ := (intervalIntegral.integral_of_le hab.le).symm
    _ > 0 := by
      apply intervalIntegral.integral_pos hab (by fun_prop)
      · intro x hx; rw [Set.IccExtend_of_mem _ _ (Set.mem_Icc_of_Ioc hx)]
        exact mul_nonneg (mul_self_nonneg _) (hu _).le
      · use c, hc; rw [Set.IccExtend_of_mem _ _ hc]
        exact mul_pos (mul_self_pos.mpr hf) (hu _)

open InnerProductGeometry in
theorem Zad6 : angle !₂[(1 : ℝ), 2, 3] !₂[3, -1, 2] = π / 3 := by
  simp [angle, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]; norm_num
  apply arccos_eq_of_eq_cos <;> bound

open scoped Zad3 in
theorem Zad8 : (ℝ ∙ !![(4 : ℝ), 2; -2, 1]).starProjection !![-2, 1; 0, 2] =
    !![-(16 / 25), -(8 / 25); 8 / 25, -(4 / 25)] := by
  norm_num [Submodule.starProjection_singleton, trace, mul_apply]

theorem Zad9 [CommRing R] [NoZeroDivisors R] [Fintype n] [DecidableEq n] {A : Matrix n n R}
    (h : Aᵀ * A = 1) : A.det = 1 ∨ A.det = -1 := by
  apply_fun det at h; simp_all [← sq]

theorem Zad10 [CommRing R] [LinearOrder R] [AddLeftMono R] [PosMulMono R] [NoZeroDivisors R]
    [Fintype n] {A : Matrix n n R} : (Aᵀ * A).trace = (A * A).trace ↔ A.IsSymm where
  mpr h := congr(($h * A).trace)
  mp h := by apply eq_of_sub_eq_zero; rw [← Zad2]; simp [sub_mul, mul_sub, trace_mul_comm A, h]

alias ZadD2ab := ALG1.Cwi7.Zad3a_symm
alias ZadD2ab_basis := SymmMatrix.basis

theorem ZadD2c (n : Type*) [Fintype n] :
    Module.finrank ℝ (SymmMatrix n ℂ) = Fintype.card n * (Fintype.card n + 1) := by
  rw [finrank_real_of_complex, ZadD2ab, mul_comm, Nat.choose_succ_right_eq, mul_comm]; simp

noncomputable def ZadD2c_basis (n : Type*) [Fintype n] :=
  Complex.basisOneI.smulTower (ZadD2ab_basis n ℂ)
