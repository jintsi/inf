import Inf.AM1.Tendsto
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Inf.AM2.LocalExtr
import Mathlib.Analysis.Calculus.Deriv.Pi

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

/-
theorem Zad6b : IsLocalExtr (fun (x, y, z) => x ^ 2 + y ^ 2 + z ^ 3 + 2 * x + 6 * y * z) (x, y, z)
    ↔ ((x, y, z) : ℝ × ℝ × ℝ) = (-1, -18, 6) := by
  constructor
  · intro h; have := h.fderiv_eq_zero; congr 1
    · have hx := congr($this (1, 0, 0)); rw [fderiv_apply_eq_deriv (by fun_prop)] at hx
      simp [add_right_comm _ (z ^ 3)] at hx; simp [add_right_comm _ (y ^ 2),
        deriv_comp_const_add (f := fun t => t ^ 2 + 2 * t) (a := x)] at hx
      rw [deriv_fun_add (g := fun t => 2 * t) (by simp) (by fun_prop)] at hx; simp at hx; linarith
    have hy := congr($this (0, 1, 0)); rw [fderiv_apply_eq_deriv (by fun_prop)] at hy
    simp [add_right_comm _ (2 * x), add_comm (x ^ 2), add_assoc _ (x ^ 2)] at hy
    simp [add_right_comm _ (_ + _), deriv_comp_const_add (f := fun t => t ^ 2 + 6 * t * z)] at hy
    rw [deriv_fun_add (by simp) (by fun_prop)] at hy; simp at hy
    have hz := congr($this (0, 0, 1)); rw [fderiv_apply_eq_deriv (by fun_prop)] at hz
    simp [add_assoc] at hz; simp [← add_assoc, add_right_comm _ (2 * x), deriv_comp_const_add
      (f := fun t => t ^ 3 + 6 * y * t)] at hz
    rw [deriv_fun_add (g := (6 * y * ·)) (by simp) (by fun_prop)] at hz; simp at hz
    have : 3 * z * (z - 6) = 0 := by linear_combination hz - 3 * hy
    simp [sub_eq_zero] at this; rcases this with rfl | rfl; swap
    · norm_num [← eq_neg_iff_add_eq_zero, mul_comm, ← eq_div_iff_mul_eq] at hy; simpa
    simp at hy; subst y; sorry
  · intro h; simp at h; rcases h with ⟨rfl, rfl, rfl⟩; apply Or.inl
    let b : Module.Basis (Fin 3) ℝ (ℝ × ℝ × ℝ) := .ofEquivFun {
      toFun := fun (x, y, z) => ![x, y, z], map_add' := by simp, map_smul' := by simp
      invFun := fun v => (v 0, v 1, v 2), right_inv := by intro v; simp; ext i; fin_cases i <;> rfl}
    apply isLocalMin_of_hessian b (by fun_prop)
    · simp; repeat rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
      rw [fderiv_fun_pow, fderiv_fun_pow, fderiv_fun_pow, fderiv_const_mul, fderiv_fun_mul,
        fderiv_const_mul] <;> try fun_prop
      simp [fderiv.fst, fderiv.snd]; rw [← ContinuousLinearMap.coe_inj]; apply b.ext
      intro i; fin_cases i <;> norm_num [b]
    simp; have : ContDiffAt ℝ 2 (fun x : (ℝ × ℝ × ℝ) => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 3 + 2 * x.1 + 6 * x.2.1 * x.2.2) (-1, -18, 6) :=
      by fun_prop
    use this.isSymm_hessian; simp [hessian, this.fderiv_fderiv_apply_same]; sorry
-/

theorem Zad6c : IsLocalExtr (fun (x : Fin n → ℝ) => ∑ i, x i ^ 4 - 4 * ∑ i, x i) x ↔ x = 1 := by
  constructor
  · intro h; have := h.fderiv_eq_zero
    ext i; apply_fun fun f => f (Pi.single i 1) at this
    rw [fderiv_apply_eq_deriv (by fun_prop)] at this
    simp [Pi.single_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, add_ite, ite_sub_ite] at this
    simp [Finset.sum_ite, Finset.filter_eq', deriv_comp_const_add (fun x : ℝ => x ^ 4 - 4 * x),
      deriv_fun_sub, differentiableAt_fun_id.const_mul (E := ℝ), ← mul_sub_one, sub_eq_zero,
      pow_eq_one_iff_of_ne_zero, show ¬Even 3 from Nat.not_even_two_mul_add_one 1] at this; simpa
  · intro rfl; apply Or.inl; apply isLocalMin_of_hessian (Pi.basisFun ℝ (Fin n)) (by fun_prop)
    · simp (maxDischargeDepth := 3) [fderiv_fun_sub, fderiv_fun_sum, fderiv_fun_pow, fderiv_apply,
        fderiv_const_mul, differentiableAt_apply, Finset.smul_sum]
    convert Matrix.PosDef.ofNat (R := ℝ) (n := Fin n) 12; ext i j; simp [hessian]
    simp [Matrix.ofNat_apply]; split_ifs with h
    · subst j; rw [fderiv_fderiv_apply_same (by filter_upwards; fun_prop) (by fun_prop)]; eta_expand
      simp [Pi.single_apply, add_ite, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
      conv_lhs =>
        arg 1; ext x; rw [deriv_fun_sub (by fun_prop) (by fun_prop)]; simp
        rw [deriv_fun_pow (f := (1 + ·)) (by fun_prop)]
      simp; rw [deriv_fun_pow (by fun_prop)]; eta_expand; norm_num
    rw [fderiv_apply_eq_deriv (by fun_prop),
      ← sub_eq_of_eq_add (deriv_clm_apply (by fun_prop) (differentiableAt_const _))]; simp
    convert funext_iff.mp deriv_zero (0 : ℝ) with x
    rw [fderiv_apply_eq_deriv (by fun_prop)]
    simp [Finset.mul_sum, ← Finset.sum_sub_distrib]; rw [deriv_fun_sum (by fun_prop)]
    simp [Pi.single_apply j, add_ite, ite_sub_ite, h,
      ← fun P [Decidable P] (f g : ℝ → ℝ) => funext (ite_apply P f g), apply_ite deriv, ite_apply]
    rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_fun_pow (f := (1 + ·)) (by fun_prop)]; simp
