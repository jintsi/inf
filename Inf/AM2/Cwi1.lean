import Inf.AM2.RiemannIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

lemma Finset.sum_range_natCast [DivisionRing R] [NeZero (2 : R)] (n : ℕ) :
    ∑ i ∈ range n, (i : R) = n * (n - 1) / 2 := by
  rw [← Nat.cast_sum, eq_div_iff two_ne_zero, ← Nat.cast_ofNat, ← Nat.cast_mul, sum_range_id_mul_two]
  cases n <;> simp

open Topology Filter Finset Real intervalIntegral

namespace AM2.Cwi1

theorem Zad1 : ∫ x in 1..3, 2 * x - 1 = 6 := by
  apply tendsto_nhds_unique (tendsto_sum_left_intervalIntegral (by simp) (by fun_prop))
  norm_num only
  simp_rw [smul_eq_mul, sub_eq_add_neg, ← sum_add_card_nsmul, mul_add, ← card_nsmul_add_sum,
    div_eq_inv_mul, ← mul_sum, card_range, nsmul_eq_mul, sum_range_natCast]
  field_simp; ring_nf
  convert (tendsto_atTop_of_eventually_const (X := ℝ) (i₀ := 1) ?_).sub
    (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.mul_const 4)
  · simp; rfl
  · intro i hi; field_simp

theorem Zad2a : Tendsto (fun n => ∑ i ∈ range n, n / (n ^ 2 + (i + 1) ^ 2 : ℝ)) atTop (𝓝 (π / 4)) := by
  apply Tendsto.congr' (f₁ := fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ range n, (1 + ((i + 1) / n) ^ 2 : ℝ)⁻¹)
  · simp_rw [EventuallyEq, eventually_atTop, smul_eq_mul, mul_sum]
    use 1; intro n hn; field_simp
  convert tendsto_sum_right_intervalIntegral_zero_one (f := fun x => (1 + x ^ 2)⁻¹)
    (by fun_prop (disch := intros; positivity))
  simp

theorem Zad2b : Tendsto (fun n => π / n * ∑ i ∈ range n, sin ((i + 1) * π / n)) atTop (𝓝 2) := by
  simp_rw [mul_comm]
  convert tendsto_sum_right_intervalIntegral_zero pi_pos continuousOn_sin
  norm_num

theorem Zad2c : Tendsto (fun n : ℕ => (n * √n)⁻¹ * ∑ i ∈ range n, √(2 * i + 1)) atTop (𝓝 (2 * √2 / 3)) := by
  apply Tendsto.congr (f₁ := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, √(2 * ((i + 2⁻¹) / n)))
  · intro n; simp only [mul_sum, ← mul_div_assoc, sqrt_div', Nat.cast_nonneg]; grind
  convert tendsto_sum_midpoint_intervalIntegral zero_lt_one
    (f := fun x => √(2 * x)) (by fun_prop) using 1
  · funext; simp
  · simp only [Nat.ofNat_nonneg, sqrt_mul, intervalIntegral.integral_const_mul]
    simp_rw [sqrt_eq_rpow]; rw [integral_rpow (by norm_num)]; norm_num; ring

theorem Zad2d : Tendsto (fun n : ℕ => ∑ i ∈ range n, (2 * i + 1 + n : ℝ)⁻¹) atTop (𝓝 (log 3 / 2)) := by
  apply Tendsto.congr' (f₁ := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, ((2 * i + 1) / n + 1 : ℝ)⁻¹)
  · simp_rw [EventuallyEq, eventually_atTop, mul_sum]
    use 1; intro n hn; field_simp
  convert tendsto_sum_midpoint_intervalIntegral zero_lt_one
    (f := fun x => (2 * x + 1)⁻¹) (by fun_prop (disch := grind)) using 6
  · funext; simp
  · ring
  · simp; ring_nf

theorem Zad2e : Tendsto (fun n : ℕ => ∑ i ∈ range n, (√(2 * n ^ 2 - (i + 1) ^ 2))⁻¹) atTop (𝓝 (π / 4)) := by
  apply Tendsto.congr' (f₁ := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, (√(2 - ((i + 1) / n) ^ 2))⁻¹)
  · simp_rw [EventuallyEq, eventually_atTop, mul_sum]
    use 1; intro n hn; nth_rw 1 [← Real.sqrt_sq (n.cast_nonneg)]
    simp_rw [← mul_inv, ← Real.sqrt_mul (sq_nonneg _)]; field_simp
  convert ←  tendsto_sum_right_intervalIntegral_zero_one (f := fun x => (√(2 - x ^ 2))⁻¹)
    (ContinuousOn.inv₀ (by fun_prop) ?_)
  · calc ∫ x in 0..1, (√(2 - x ^ 2))⁻¹
    _ = ∫ x in 0..1, (√2 * √(1 - (x / √ 2) ^ 2))⁻¹ := by
      congr! 3 with x; rw [← sqrt_mul two_pos.le, div_pow, sq_sqrt two_pos.le]; field_simp
    _ = ∫ x in 0..(√2)⁻¹, deriv arcsin x := by
      simp_rw [mul_inv]
      rw [integral_const_mul, integral_comp_div (fun x => (√(1 - x ^ 2))⁻¹) (sqrt_ne_zero'.mpr two_pos)]
      simp
    _ = π / 4 := by
      rw [intervalIntegral.integral_deriv_eq_sub' _ rfl]
      · rw [arcsin_zero, sub_zero, ← arcsin_eq_of_sin_eq sin_pi_div_four, sqrt_div_self]
        simp; ring_nf; and_intros <;> gcongr 1 <;> norm_num
      · simp [differentiableAt_arcsin]; intro x h1 h2; use (neg_one_lt_zero.trans_le h1).ne'
        intro h; subst h; absurd h2; simp [← sqrt_div_self, div_lt_one₀, sqrt_lt']; norm_num
      · simp only [deriv_arcsin, one_div, inv_nonneg, sqrt_nonneg, Set.uIcc_of_le]
        apply ContinuousOn.inv₀ (by fun_prop)
        simp +contextual [← sqrt_inv, le_sqrt, sqrt_ne_zero', -sq_lt_one_iff_abs_lt_one]; bound
  · simp only [Set.mem_Icc, ne_eq, sqrt_ne_zero', sub_pos, and_imp]; intro x h0 h1
    exact ((sq_le_one_iff₀ h0).mpr h1).trans_lt one_lt_two

theorem Zad2f : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ((2 * n).factorial / n.factorial) ^ (n : ℝ)⁻¹)
    atTop (𝓝 (4 / exp 1)) := by
  apply Tendsto.congr' (f₁ := fun n : ℕ => (∏ i ∈ range n, (n + 1 + i) / n : ℝ) ^ (n : ℝ)⁻¹)
  · simp_rw [EventuallyEq, eventually_atTop, prod_div_distrib, prod_const, card_range]
    use 1; intro n hn; rw [div_rpow, pow_rpow_inv_natCast, div_eq_inv_mul] <;> try positivity
    congr; field_simp; norm_cast
    rw [← Nat.ascFactorial_eq_prod_range, mul_comm, Nat.factorial_mul_ascFactorial, two_mul]
  apply Tendsto.congr' (f₁ := fun n : ℕ => exp ((∑ i ∈ range n, log (1 + (i + 1) / n)) * (n : ℝ)⁻¹))
  · simp_rw [EventuallyEq, eventually_atTop, exp_mul, exp_sum, add_right_comm, add_assoc, add_div]
    use 1; intro n hn; congr! 2; rw [exp_log, div_self] <;> positivity
  convert_to Tendsto _ _ (𝓝 (exp (log 2 * 2 - 1)))
  · norm_num [exp_sub, exp_mul, exp_log]
  apply Tendsto.rexp; simp_rw [mul_comm]
  convert tendsto_sum_right_intervalIntegral_zero_one (f := fun x => log (1 + x))
    (by fun_prop (disch := simp; intros; positivity))
  norm_num; linarith

theorem Zad3a : ∫ x in 0..π/3, sin x ^ 3 * cos x ^ 2 = 47 / 480 := by
  norm_num [integral_sin_pow_odd_mul_cos_pow 1, mul_sub, ← pow_add]

theorem Zad3b : ∫ x in 0..1, x ^ 5 / √(3 * x ^ 3 + 1) = 8 / 81 := by calc
  ∫ x in 0..1, x ^ 5 / √(3 * x ^ 3 + 1)
  _ = ∫ x in 0..1, x ^ 3 / (3 * √(3 * x ^ 3 + 1)) * (3 * x ^ 2) := by ring_nf
  _ = ∫ x in 0..1, x / (3 * √(3 * x + 1)) := by
    convert integral_comp_mul_deriv_of_deriv_nonneg (continuousOn_pow 3) (fun x _ => hasDerivAt_pow 3 x)
      (by simp [sq_nonneg]) using 4 <;> simp
  _ = ∫ x in 0..1, (3 * x + 1 - 1) / (9 * √(3 * x + 1)) := by ring_nf
  _ = 27⁻¹ * ∫ x in 1..4, (x - 1) / √x := by
    rw [integral_comp_mul_add (fun x => (x - 1) / (9 * √x)) three_ne_zero]
    simp [← integral_const_mul]; ring_nf
  _ = 27⁻¹ * ∫ x in 1..4, x ^ (2 : ℝ)⁻¹ - x ^ (-(2 : ℝ)⁻¹) := by
    rw [integral_congr]; simp [Set.EqOn, sub_div]; simp [sqrt_eq_rpow]
    intro x h _; symm; apply rpow_neg; positivity
  _ = 8 / 81 := by
    rw [integral_sub (intervalIntegrable_rpow (by simp)) (intervalIntegrable_rpow (by simp)),
      integral_rpow (by norm_num), integral_rpow (by norm_num)]
    norm_num

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}

theorem Zad4 {a : ℝ} (hf : ∀ x ∈ Set.uIcc (-a) a, f (-x) = -f x) : ∫ x in -a..a, f x = 0 := calc ∫ x in -a..a, f x
  _ = (2 : ℝ)⁻¹ • ((∫ x in -a..a, f x) + ∫ x in -a..a, f x) := by rw [← two_smul ℝ, smul_smul]; simp
  _ = (2 : ℝ)⁻¹ • ((∫ x in -a..a, f x) - ∫ x in -a..a, -f x) := by
    simp_rw [sub_eq_add_neg, ← integral_neg, neg_neg]
  _ = (2 : ℝ)⁻¹ • ((∫ x in -a..a, f x) - ∫ x in -a..a, f (-x)) := by rw [integral_congr hf]
  _ = (2 : ℝ)⁻¹ • ((∫ x in -a..a, f x) - ∫ x in -a..a, f x) := by rw [integral_comp_neg, neg_neg]
  _ = 0 := by simp

theorem Zad5 {a : ℝ} (hc : ContinuousOn f (Set.uIcc (-a) a)) (hf : ∀ x ∈ Set.uIcc (-a) a, f (-x) = f x) :
    ∫ x in -a..a, f x = 2 • ∫ x in 0..a, f x := calc ∫ x in -a..a, f x
  _ = (∫ x in -a..0, f x) + ∫ x in 0..a, f x := by
    apply (integral_add_adjacent_intervals (hc.mono ?_).intervalIntegrable (hc.mono ?_).intervalIntegrable).symm
    · apply Set.uIcc_subset_uIcc_left; simpa [Set.mem_uIcc] using le_total 0 a
    · apply Set.uIcc_subset_uIcc_right; simpa [Set.mem_uIcc] using le_total 0 a
  _ = (∫ x in -a..0, f (-x)) + ∫ x in 0..a, f x := by
    rw [integral_congr (Set.EqOn.mono ?_ hf)]
    apply Set.uIcc_subset_uIcc_left; simpa [Set.mem_uIcc] using le_total 0 a
  _ = 2 • ∫ x in 0..a, f x := by rw [two_nsmul, integral_comp_neg, neg_zero, neg_neg]

theorem Zad6 : ∫ x in -π..π, sin x ^ 7 / (5 + 3 * cos x) = 0 :=
  Zad4 fun x _ => by simp [neg_pow (sin x), (show Odd 7 by decide).neg_one_pow, neg_div]

theorem Zad7 : ∫ x in 0..π / 2, f (sin x) = ∫ x in 0..π/2, f (cos x) := by
  simp_rw [← cos_pi_div_two_sub, integral_comp_sub_left fun x => f (cos x), sub_self, sub_zero]

theorem Zad8_step (n : ℕ) : ∫ x in 0..π / 2, cos x ^ (n + 2)
    = (n + 1) / (n + 2) * ∫ x in 0..π / 2, cos x ^ n := by simp [integral_cos_pow]

open Nat in
theorem Zad8_even (n : ℕ) : ∫ x in 0..π / 2, cos x ^ (2 * n) = (2 * n - 1)‼ / (2 * n)‼ * (π / 2) := by
  induction n
  case zero => simp
  case succ n ih => simp_rw [mul_add_one, Zad8_step, ih, Nat.reduceSubDiff,
    doubleFactorial_add_two, doubleFactorial_add_one]; grind

open Nat in
theorem Zad8_odd (n : ℕ) : ∫ x in 0..π / 2, cos x ^ (2 * n + 1) = (2 * n)‼ / (2 * n + 1)‼ := by
  induction n
  case zero => simp
  case succ n ih => simp_rw [mul_add_one, add_right_comm, Zad8_step, ih, doubleFactorial_add_two]; grind

theorem Zad9 {a b : ℝ} {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.uIcc a b))
    (hg : ContinuousOn g (Set.uIcc a b)) (hg0 : ∀ x ∈ Set.uIoc a b, 0 ≤ g x) :
    ∃ c ∈ Set.uIcc a b, ∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x :=
  exists_eq_const_mul_intervalIntegral_of_nonneg hf hg.intervalIntegrable hg0

theorem Zad10 : ∫ x in π..2 * π, exp (-x ^ 2) * cos x ^ 2 < ∫ x in 0..π, exp (-x ^ 2) * cos x ^ 2 := calc
  ∫ x in π..2 * π, exp (-x ^ 2) * cos x ^ 2 = ∫ x in 0..π, exp (-(x + π) ^ 2) * cos x ^ 2 := by
    symm; convert integral_comp_add_right _ π using 2 <;> simp [two_mul]
  _ < ∫ x in 0..π, exp (-x ^ 2) * cos x ^ 2 := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt pi_pos (by fun_prop) (by fun_prop)
    · simp_rw [Set.mem_Ioc, and_imp]; intro x hl hu; gcongr; simp [pi_nonneg]
    · use 0, Set.left_mem_Icc.mpr pi_nonneg; gcongr <;> simp [pi_pos]

theorem Zad11 : Tendsto (fun n => ∫ x in 0..1, x ^ n / (1 + x)) atTop (𝓝 0) := by
  apply Tendsto.squeeze tendsto_const_nhds (h := fun n => ∫ x in 0..1, x ^ n)
  · simpa using (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  · intro n; apply integral_nonneg zero_le_one; simp_rw [Set.mem_Icc, and_imp]; intro x hl hu; positivity
  · intro n; apply integral_mono_on zero_le_one
      (ContinuousOn.intervalIntegrable (by fun_prop (disch := simp; intros; linarith)))
      (ContinuousOn.intervalIntegrable (by fun_prop))
    simp_rw [Set.mem_Icc, and_imp]; intro x hl hu; bound
