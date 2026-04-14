import Inf.AM2.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Inf.AM1.Cwi3

open Topology Filter SummationFilter Finset Real

/-! ## Implementation notes

Unqualified `Summable f` means that the series `∑' n, f n` converges _absolutely_ - since that's
the mode that doesn't depend on the ordering of the summands and therefore generalizes more readily
to domains other than `ℕ`.

Thus, a series being convergent is denoted `Summable f (conditional ℕ)`,
divergent `¬Summable f (conditional ℕ)`, convergent absolutely `Summable f`,
and convergent conditionally `Summable f (conditional ℕ) ∧ ¬Summable f`. -/

namespace AM2.Cwi4

theorem Zad1a : Summable (fun (n : ℕ) => ((3 * n - 2) * (3 * n + 1) : ℝ)⁻¹) (conditional ℕ) := by
  apply Summable.congr (f := fun (n : ℕ) => (9 * (n : ℝ) - 6)⁻¹ - (9 * (↑(n + 1) : ℝ) - 6)⁻¹) ?_
  · intro n; push_cast; field (disch := norm_cast <;> lia)
  simp_rw [summable_conditional_iff, sum_range_sub']; use -6⁻¹; simp
  exact (tendsto_natCast_atTop.const_mul_atTop' (show 0 < (9 : ℝ) by simp)).atTop_sub_const 6
    |>.inv_atTop.const_sub_zero (-6⁻¹)

theorem Zad1b : Summable (fun (n : ℕ) => (1 + (-1) ^ n) / π ^ n) := by
  convert (summable_geometric_of_abs_lt_one (r := π⁻¹) ?pi).add
    (summable_geometric_of_abs_lt_one (r := -π⁻¹) (abs_neg π⁻¹ ▸ ?pi)) using 2 with n
  · ring
  · simp [inv_lt_one₀, pi_pos, lt_abs]; left; apply two_le_pi.trans_lt'; simp

theorem Zad2a : ¬Summable (fun (n : ℕ) => arccos (√n)⁻¹) (conditional ℕ) := by
  apply mt Summable.tendsto_atTop_zero'
  apply mt (tendsto_nhds_unique (b := π / 2)); simp only [pi_div_two_pos.ne, imp_false, not_not]
  exact arccos_zero ▸ tendsto_natCast_atTop.sqrt_atTop.inv_atTop.arccos

theorem Zad2b : Summable (fun (n : ℕ) => (n * √n + sin n.factorial) / (3 * n ^ 3 - 2)) := by
  apply Summable.of_nonneg_atTop_of_le_atTop (f := fun n => 2 * n ^ (3 / 2 : ℝ) / (2 * n ^ 3))
  · filter_upwards [eventually_ge_atTop 2] with n hn; apply div_nonneg
    · grw [← neg_one_le_sin, ← hn]; simp; bound
    · grw [← hn]; norm_num
  · filter_upwards [eventually_ge_atTop 2] with n hn; rw [two_mul]
    refine div_le_div₀ (by bound) (add_le_add ?_ ?_) (by bound) ?_
    · apply le_of_eq; rw [sqrt_eq_rpow, ← rpow_one_add'] <;> bound
    · grw [sin_le_one, ← hn, ← show (1 : ℝ) ≤ 3 / 2 by norm_num] <;> simp
    · rw [le_sub_comm]; ring_nf; grw [← hn]; norm_num
  apply (by norm_num : Summable fun (n : ℕ) => 1 / (n : ℝ) ^ (3 / 2 : ℝ)).congr
  intro n; field_simp; rw [one_div, ← rpow_neg, ← rpow_ofNat, ← rpow_sub'] <;> norm_num

theorem Zad2c : ¬Summable (fun (n : ℕ) => (log n ^ 7)⁻¹) (conditional ℕ) := by
  rw [← summable_iff_conditional_of_nonneg_atTop]; swap
  · simp; use 1; bound
  apply mt (Summable.of_nonneg_atTop_of_le_atTop (g := fun n => n⁻¹) (by simp) ?_) not_summable_natCast_inv
  filter_upwards [eventually_gt_atTop 1,
    tendsto_natCast_atTop.eventually (isLittleO_log_rpow_rpow_atTop 7 one_pos).eventuallyLE] with n hn
  simp only [rpow_ofNat, norm_pow, norm_eq_abs, rpow_one, RCLike.norm_natCast]
  rw [abs_of_nonneg (by positivity)]; exact inv_anti₀ (pow_pos (log_pos (by simpa)) 7)

theorem Zad2d : Summable (fun (n : ℕ) => log (1 + 1 / n) / n) := by
  refine Summable.of_nonneg_of_le (f := fun (n : ℕ) => 1 / n ^ 2) (by bound) ?_ (by simp)
  intro n; grw [log_le_sub_one_of_pos (by positivity)]; simp; field_simp; rfl

theorem Zad2e : ¬Summable (fun n => 4 ^ n * sin (π / 3 ^ n)) (conditional ℕ) := by
  apply mt Summable.tendsto_atTop_zero'; apply not_tendsto_nhds_of_tendsto_atTop
  apply tendsto_atTop_mono' (f₁ := fun n => 4 ^ n * 2 / 3 ^ n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    grw [← mul_le_sin (by bound) (by grw [← hn]; bound; simp)]; field_simp; rfl
  · simp_rw [mul_div_right_comm, ← div_pow]
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).atTop_mul_const two_pos

theorem Zad3 {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (h : Summable f) : Summable (fun n => √(f n * f (n + 1))) := by
  refine Summable.of_nonneg_of_le (f := fun (n : ℕ) => (f n + f (n + 1)) / 2) (by bound) ?_ ?_
  · intro n; rw [sqrt_le_left (by bound)]; field_simp; grw [← four_mul_le_sq_add]; ring_nf; rfl
  · exact (h.add (h.shift 1)).div_const 2

/-- **Zad. 4**, the form from the exercise sheet can be recovered from the fact that
for nonnegative series, absolute and conditional convergence are the same (`summable_iff_conditional_of_nonneg`) -/
theorem _root_.Summable.of_tendsto_div {f g : ℕ → ℝ} (hgf : Tendsto (fun n => g n / f n) atTop (𝓝 a))
    (hf : ∀ᶠ n in atTop, f n ≠ 0) (h : Summable f) : Summable g := by
  rw [← Nat.cofinite_eq_atTop] at hgf
  have : Summable (fun n => f n * (g n / f n)) := by
    apply Summable.mul_tendsto_const ?_ hgf; exact h.abs
  apply this.congr_atTop; filter_upwards [hf] with n hn; field

theorem Zad4 {f g : ℕ → ℝ} (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 a))
    (ha : a ≠ 0) (hg : ∀ᶠ n in atTop, g n ≠ 0) : Summable f ↔ Summable g := by
  constructor; case mpr => exact .of_tendsto_div hfg hg
  apply Summable.of_tendsto_div ((hfg.inv₀ ha).congr (by simp))
  filter_upwards [hfg.eventually_ne ha]; simp +contextual

theorem Zad5a : ¬Summable
    (fun n => 4 ^ n * (2 * n - 1).factorial / n ^ (2 * n) : ℕ → ℝ) (conditional ℕ) := by
  rw [← summable_iff_conditional_of_nonneg (by bound)]
  apply not_summable_of_ratio_test_tendsto_gt_one (l := 16 / exp 1 ^ 2)
  · grw [exp_one_lt_three]; norm_num
  simp only [norm_div, norm_mul, norm_pow, norm_ofNat, RCLike.norm_natCast]; push_cast
  apply Tendsto.congr' (f₁ := fun (n : ℕ) => 8 * (2 - (3 - (n + 1 : ℝ)⁻¹) / (n + 1)) /
      ((1 + 1 / n) ^ n) ^ 2)
  · filter_upwards [eventually_ne_atTop 0] with n hn; symm; calc
    4 ^ (n + 1) * (2 * (n + 1) - 1).factorial / (n + 1) ^ (2 * (n + 1)) /
      (4 ^ n * (2 * n - 1).factorial / n ^ (2 * n) : ℝ)
    _ = 4 ^ (n + 1) / 4 ^ n * ((2 * n + 1).factorial / (2 * n - 1).factorial) /
      ((n + 1) ^ (2 + 2 * n) / n ^ (2 * n)) := by grind
    _ = 4 * (2 * n * (2 * n + 1)) / ((n + 1) ^ 2 * (1 + 1 / n) ^ (2 * n)) := by
      congr
      · field
      · rw [show 2 * n = 2 * n - 1 + 1 by lia, Nat.factorial_succ, Nat.factorial_succ,
          show 2 * n - 1 + 1 = 2 * n by lia]; push_cast; field
      · rw [pow_add, mul_div_assoc, ← div_pow, add_div, div_self]; simpa
    _ = 8 * (2 - (3 - (n + 1 : ℝ)⁻¹) / (n + 1)) / ((1 + 1 / n : ℝ) ^ n) ^ 2 := by field
  convert ((tendsto_natCast_add_atTop 1).inv_atTop.const_sub 3).div_atTop (tendsto_natCast_add_atTop 1)
    |>.const_sub_zero 2 |>.const_mul 8 |>.div ((tendsto_one_add_div_pow_exp 1).pow 2) (by simp)
  norm_num

theorem Zad5b : Summable (fun n => ((n - 2) / (n + 2)) ^ (n * (n + 3)) : ℕ → ℝ) := by
  apply Summable.congr
    (f := fun (n : ℕ) => ((1 + (-4) / (n + 2)) * (1 + (-4) / ↑(n + 2)) ^ (n + 2) : ℝ) ^ n) ?_
  · intro n; rw [mul_comm n, pow_mul]; push_cast; field_simp; ring
  apply summable_pow_of_tendsto
  · exact (((tendsto_natCast_add_atTop 2).const_div_atTop (-4)).const_add_zero 1).one_mul
      ((tendsto_one_add_div_pow_exp (-4)).comp (tendsto_add_atTop_nat 2))
  · simp

theorem Zad5c : Summable (fun (n : ℕ) => n ^ (n - 1 / n : ℝ) / √(4 * n ^ 2 + 2 * n - 1) ^ (n + 1)) := by
  apply Summable.of_nonneg_atTop_of_le_atTop (f := fun n => n ^ n / √(4 * n ^ 2) ^ n)
  · filter_upwards with n; positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn; gcongr
    · rw [← rpow_natCast]; gcongr <;> simp [hn]
    grw [pow_le_pow_right₀ (by grw [← hn]; simp) (n.le_succ)]; gcongr
    rw [le_sub_iff_add_le]; norm_cast; lia
  apply Summable.congr_atTop (f₁ := fun n => (1 / 2) ^ n) (summable_geometric_of_lt_one (by simp) (by norm_num))
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [sqrt_mul, sqrt_sq, ← div_pow, div_mul_cancel_right₀, show (4 : ℝ) = 2 * 2 by norm_num]
    <;> simp [hn]

theorem Zad5d : ¬Summable (fun n => 9 ^ n * n ^ 5 / (6 + (-1) ^ n) ^ n : ℕ → ℝ) (conditional ℕ) := by
  apply mt Summable.tendsto_atTop_zero'; apply not_tendsto_nhds_of_tendsto_atTop
  apply tendsto_atTop_mono (f := (fun n => 9 ^ n * n ^ 5 / 7 ^ n : ℕ → ℝ))
  · intro n; cases neg_one_pow_eq_or ℝ n <;> norm_num [*]; gcongr; norm_num
  simp_rw [mul_div_right_comm, ← div_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).atTop_mul_atTop₀
    (tendsto_natCast_atTop.atTop_pow₀ 5)

theorem Zad5e : Summable (fun (n : ℕ) => cos (√n)⁻¹ / n ^ arctan n) := by
  apply Summable.of_nonneg_atTop_of_le_atTop (f := fun n => 1 / n ^ (π / 3))
  · filter_upwards [eventually_ge_atTop 1] with n hn; refine div_nonneg ?_ (by bound)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by trans 0 <;> simp [pi_div_two_pos.le])
    grw [← hn, two_le_pi]; simp
  · filter_upwards [eventually_ge_atTop ⌈√3⌉₊, eventually_ge_atTop 1] with n hn hn1
    grw [cos_le_one]; gcongr; · simpa
    grw [← Nat.le_of_ceil_le hn]; simp
  · grw [summable_one_div_nat_rpow, ← pi_gt_d2]; norm_num

theorem Zad5f : ¬Summable (fun (n : ℕ) => n * (cbrt (n ^ 3 + 1) - n)) (conditional ℕ) := by
  unfold cbrt
  rw [← summable_iff_conditional_of_nonneg fun n => mul_nonneg (by simp) (sub_nonneg_of_le ?_)]; swap
  · rw [le_rpow_inv_iff_of_pos] <;> bound
  apply mt (Summable.of_nonneg_atTop_of_le_atTop (g := fun (n : ℕ) => (4 * n)⁻¹) (by bound) _)
  · simp; rw [summable_mul_right_iff (by norm_num)]; exact not_summable_natCast_inv
  filter_upwards [eventually_ge_atTop 1] with n hn; calc (4 * n : ℝ)⁻¹
    _ = n * (n + (4 * n ^ 2 : ℝ)⁻¹ - n) := by field
    _ = n * (((n + (4 * n ^ 2 : ℝ)⁻¹) ^ 3) ^ ((3 : ℕ)⁻¹ : ℝ) - n) := by
      rw [pow_rpow_inv_natCast] <;> bound
    _ ≤ n * ((n ^ 3 + 1) ^ (3⁻¹ : ℝ) - n) := by
      gcongr; apply rpow_le_rpow (by bound) _ (by bound)
      field_simp; ring_nf; norm_cast
      suffices 1 + n ^ 3 * 12 ≤ n ^ 6 * 4 + n ^ 6 * 12 by grw [this]; ring_nf; rfl
      gcongr <;> bound

theorem Zad6 : Tendsto (fun n => 3 ^ n / n ^ 2026 : ℕ → ℝ) atTop atTop := by
  apply Tendsto.congr fun n => inv_div _ _
  apply Tendsto.inv_tendsto_nhdsGT_zero; rw [tendsto_nhdsWithin_iff]; symm; and_intros
  · filter_upwards [eventually_gt_atTop 0]; simp +contextual
  apply tendsto_pow_const_div_const_pow_of_one_lt; simp

theorem Zad7a {a : ℝ} (ha : 0 < a) : Summable (fun n => a ^ n * Nat.factorial n / n ^ n) ↔ a < exp 1 := by
  have ratio : ∀ (n : ℕ), a ^ (n + 1) * (n + 1).factorial / (n + 1) ^ (n + 1) / (a ^ n * n.factorial / n ^ n)
      = a / (1 + 1 / n) ^ n := fun n => calc
    a ^ (n + 1) * (n + 1).factorial / (n + 1) ^ (n + 1) / (a ^ n * n.factorial / n ^ n)
    _ = a ^ (n + 1) / a ^ n * ((n + 1).factorial / n.factorial) / ((n + 1) ^ (n + 1) / n ^ n) := by field
    _ = a * (n + 1) / ((n + 1) * ((n + 1) / n) ^ n) := by
      congr
      · field
      · rw [Nat.factorial_succ]; push_cast; field
      · rw [pow_add, pow_one, div_pow]; ring
    _ = a / (1 + 1 / n) ^ n := by cases n; simp; field_simp
  rcases lt_trichotomy a (exp 1) with h | h | h
  · rw [iff_true_right h]; apply summable_of_ratio_test_tendsto_lt_one (l := a / exp 1)
    · bound
    · simp [ha.ne', Nat.factorial_ne_zero]
    simp only [norm_div, norm_mul, norm_pow, norm_eq_abs, abs_of_pos ha, RCLike.norm_natCast]; push_cast
    simp_rw [ratio]; exact (tendsto_one_add_div_pow_exp 1).const_div a (by simp)
  · subst h; rw [iff_false_right (lt_irrefl _)]
    apply mt (Summable.of_nonneg_of_le (g := fun _ => 1) (by simp) _)
    · simp [summable_const_iff]
    intro n; grw [exp_one_pow, ← pow_div_factorial_le_exp n (by simp) n]; field_simp; rfl
  · rw [iff_false_right h.not_gt]; apply not_summable_of_ratio_test_tendsto_gt_one (l := a / exp 1)
    · bound
    simp only [norm_div, norm_mul, norm_pow, norm_eq_abs, abs_of_pos ha, RCLike.norm_natCast]; push_cast
    simp_rw [ratio]; exact (tendsto_one_add_div_pow_exp 1).const_div a (by simp)

theorem Zad8a : ¬Summable (fun (n : ℕ) => (-1) ^ n / (n + exp 1) ^ (n⁻¹ : ℝ)) (conditional ℕ) := by
  apply mt Summable.tendsto_atTop_zero'; apply mt fun h => h.comp (tendsto_const_mul_atTop' two_pos)
  simp_rw [Function.comp_def, pow_mul, neg_one_pow_two, one_pow, one_div]
  apply mt (tendsto_nhds_unique (b := 1)); simp only [zero_ne_one, imp_false, not_not]
  suffices Tendsto (fun (n : ℕ) => (n + exp 1) ^ (n⁻¹ : ℝ)) atTop (𝓝 1) from
    this.inv_one.comp (tendsto_const_mul_atTop' two_pos)
  apply Tendsto.squeeze' (α := ℝ) (β := ℕ) (g := fun n => n ^ (1 / n : ℝ))
    (h := fun n => (2 * n) ^ (1 / n : ℝ))
  · exact tendsto_rpow_div.comp tendsto_natCast_atTop
  · convert (tendsto_rpow_div_mul_add 1 2⁻¹ 0 (by simp)).comp
      (tendsto_natCast_atTop.const_mul_atTop two_pos); simp
  · filter_upwards with n; simp; apply rpow_le_rpow <;> bound
  · filter_upwards [eventually_ge_atTop ⌈exp 1⌉₊] with n hn; grw [Nat.le_of_ceil_le hn]; simp [two_mul]

theorem Zad8b : Summable (fun n => (-1) ^ (n * (n + 1) / 2) * ((4 * n + 1) / (7 * n + 2)) ^ n : ℕ → ℝ) := by
  apply Summable.of_abs; simp only [abs_mul, abs_neg_one_pow, one_mul]; apply Summable.abs
  apply summable_pow_of_tendsto (l := 4 / 7); swap; norm_num
  apply Tendsto.congr (f₁ := fun (n : ℕ) => 4 / 7 - (49 * n + 14 : ℝ)⁻¹)
  · intro n; field
  exact ((tendsto_natCast_atTop.const_mul_atTop (by simp)).atTop_add_const _).inv_atTop.const_sub_zero _
