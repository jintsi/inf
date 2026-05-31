import Inf.AM1.Tendsto
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
--import Inf.AM2.LocalExtr

open Real Topology Filter

namespace AM2.Cwi8

theorem Zad1_zero : (fun (x, y) => x * y ^ 2 / (x ^ 2 + y ^ 4)) ((0, 0) : ℝ × ℝ) = 0 := by simp

theorem Zad1a : ¬ContinuousAt (fun (x, y) => x * y ^ 2 / (x ^ 2 + y ^ 4)) ((0, 0) : ℝ × ℝ) := by
  apply not_continuousAt_of_tendsto (l₁ := atTop.map (fun n => (1 / (n + 1) ^ 2, 1 / (n + 1)) : ℕ → ℝ × ℝ))
  · simp [Function.comp_def]; field_simp; ring_nf; exact tendsto_const_nhds
  · simp_rw [← one_div_pow]; exact (tendsto_one_div_add_atTop_nhds_zero_nat.zero_pow 2).prodMk_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
  · simp

theorem Zad1b_x : DifferentiableAt ℝ
    ((fun (x, y) => x * y ^ 2 / (x ^ 2 + y ^ 4)) ∘ (·, 0)) (0 : ℝ) := by simp [Function.comp_def]

theorem Zad1b_y : DifferentiableAt ℝ
    ((fun (x, y) => x * y ^ 2 / (x ^ 2 + y ^ 4)) ∘ (0, ·)) (0 : ℝ) := by simp [Function.comp_def]

theorem Zad1c (v : ℝ × ℝ) : LineDifferentiableAt ℝ (fun (x, y) => x * y ^ 2 / (x ^ 2 + y ^ 4)) (0, 0) v := by
  simp [LineDifferentiableAt]; field_simp; by_cases! hv : v.1 = 0; · simp [hv]
  fun_prop (disch := simpa)

theorem Zad2_zero : (fun (x, y) => x ^ 3 / (x ^ 2 + y ^ 2)) ((0, 0) : ℝ × ℝ) = 0 := by simp

theorem Zad2a_x : DifferentiableAt ℝ ((fun (x, y) => x ^ 3 / (x ^ 2 + y ^ 2)) ∘ (·, 0))
    (0 : ℝ) := by simp [Function.comp_def]; field_simp; exact differentiableAt_id

theorem Zad2a_y : DifferentiableAt ℝ ((fun (x, y) => x ^ 3 / (x ^ 2 + y ^ 2)) ∘ (0, ·))
    (0 : ℝ) := by simp [Function.comp_def]

theorem Zad2b (v : ℝ × ℝ) : LineDifferentiableAt ℝ (fun (x, y) => x ^ 3 / (x ^ 2 + y ^ 2))
    (0, 0) v := by simp [LineDifferentiableAt]; field_simp; fun_prop

theorem Zad2c : ¬DifferentiableAt ℝ (fun (x, y) => x ^ 3 / (x ^ 2 + y ^ 2)) ((0, 0) : ℝ × ℝ) := by
  simp [DifferentiableAt]; intro f hf
  have hx := hf.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_zero 0)) rfl
  apply HasDerivAt.unique (by simp [Function.comp_def]; field_simp; apply hasDerivAt_id) at hx
  have hy := hf.comp_hasDerivAt 0 ((hasDerivAt_zero 0).prodMk (hasDerivAt_id 0))
  apply HasDerivAt.unique (by simp [Function.comp_def]; apply hasDerivAt_zero) at hy
  have hmid := hf.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_id 0)) rfl
  apply HasDerivAt.unique (by
    simp [Function.comp_def]; field_simp; apply HasDerivAt.div_const; apply hasDerivAt_id) at hmid
  revert hmid; rw [← (1, 1).fst_add_snd, map_add]; simp [← hx, ← hy]

theorem Zad3a : DifferentiableAt ℝ (fun (x, y) => √(x ^ 2 + y ^ 2)) p ↔ p ≠ (0, 0) where
  mp := by
    contrapose; intro rfl
    apply mt fun hf => hf.comp 0 (by fun_prop)
    simpa [Function.comp_def, sqrt_sq_eq_abs] using not_differentiableAt_abs_zero
  mpr hp := by fun_prop (disch := simp_all [add_eq_zero_iff_of_nonneg, sq_nonneg, Prod.ext_iff])

theorem Zad3b_zero : (fun (x, y) => (x ^ 3 + y ^ 3) / (x ^ 2 + y ^ 2)) ((0, 0) : ℝ × ℝ) = 0 := by simp

theorem Zad3b {p : ℝ × ℝ} :
    DifferentiableAt ℝ (fun (x, y) => (x ^ 3 + y ^ 3) / (x ^ 2 + y ^ 2)) p ↔ p ≠ (0, 0) where
  mp := by
    simp [DifferentiableAt]; intro f hf rfl
    have hx := hf.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_zero 0)) rfl
    apply HasDerivAt.unique (by simp [Function.comp_def]; field_simp; apply hasDerivAt_id) at hx
    have hy := hf.comp_hasDerivAt 0 ((hasDerivAt_zero 0).prodMk (hasDerivAt_id 0))
    apply HasDerivAt.unique (by simp [Function.comp_def]; field_simp; apply hasDerivAt_id) at hy
    have hmid := hf.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_id 0)) rfl
    apply HasDerivAt.unique (by simp [Function.comp_def]; field_simp; apply hasDerivAt_id) at hmid
    revert hmid; rw [← (1, 1).fst_add_snd, map_add]; simp [← hx, ← hy]
  mpr hp := by fun_prop (disch := simp_all [add_eq_zero_iff_of_nonneg, sq_nonneg, Prod.ext_iff])

theorem Zad3c_zero : (fun (x, y) => (x ^ 2 + y ^ 2) * sin (x ^ 2 + y ^ 2)⁻¹) (0, 0) = 0 := by simp

theorem Zad3c : Differentiable ℝ (fun (x, y) => (x ^ 2 + y ^ 2) * sin (x ^ 2 + y ^ 2)⁻¹) := by
  intro p; by_cases! h : p ≠ 0
  · fun_prop (disch := simp_all [add_eq_zero_iff_of_nonneg, sq_nonneg, Prod.ext_iff])
  subst h; use 0; simp [hasFDerivAt_iff_tendsto, Prod.norm_def]
  apply tendsto_const_nhds.squeeze (h := fun p => 2 * max |p.1| |p.2|)
  · exact ((continuous_fst.tendsto (0 : ℝ × ℝ)).abs_zero.max_self
      ((continuous_snd.tendsto 0).abs_zero)).const_mul_zero 2
  · intro p; dsimp; positivity
  · intro p; dsimp
    grw [abs_sin_le_one, mul_one, (abs_add_eq_add_abs_iff _ _).mpr (by simp [sq_nonneg]), abs_pow,
      abs_pow, pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ |p.2|),
      pow_le_pow_left₀ (abs_nonneg _) (le_max_right |p.1| _)]; field_simp; ring_nf; rfl

theorem Zad4 (x y : ℝ) : 1 + fderiv ℝ (fun (x, y) => x * exp (x * y)) (1, 0) (x - 1, y) = x + y := by
  rw [fderiv_fun_mul, fderiv_exp, fderiv_fun_mul, fderiv_fst, fderiv_snd]; simp; ring_nf
  all_goals fun_prop

theorem Zad5_r {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (r θ : ℝ) :
    deriv (fun r => f (r * cos θ, r * sin θ)) r = fderiv ℝ f (r * cos θ, r * sin θ) (cos θ, sin θ) := by
  apply HasDerivAt.deriv; apply hf.differentiableAt.hasFDerivAt.comp_hasDerivAt
  apply HasDerivAt.prodMk <;> simp [hasDerivAt_mul_const]

theorem Zad5_th {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (r θ : ℝ) :
    deriv (fun θ => f (r * cos θ, r * sin θ)) θ = fderiv ℝ f (r * cos θ, r * sin θ) (-r * sin θ, r * cos θ) := by
  apply HasDerivAt.deriv; apply hf.differentiableAt.hasFDerivAt.comp_hasDerivAt; rw [neg_mul_comm]
  apply HasDerivAt.prodMk <;> apply HasDerivAt.const_mul <;> simp [hasDerivAt_cos, hasDerivAt_sin]
