import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Inf.AM2.InfiniteSum

open Real Topology Filter SummationFilter

namespace AM2.Cwi5

theorem Zad1a : TendstoUniformly (fun n x => √(x ^ 2 + 1 / n)) abs atTop := by
  rw [Metric.tendstoUniformly_iff]; intro e he
  filter_upwards [eventually_gt_atTop (e ^ 2)⁻¹]; intro n hn x
  have hn' : 0 < n := by grw [← hn]; positivity
  rw [dist_comm, dist_eq, abs_lt]; and_intros
  · grw [he, neg_zero, sub_pos, lt_sqrt (abs_nonneg x)]; simpa
  rw [inv_lt_comm₀ (sq_pos_of_pos he) hn', ← sqrt_lt' he] at hn
  apply hn.trans_le'; grw [sub_le_iff_le_add', sqrt_le_left (by positivity)]
  simp [add_sq, hn'.le]; positivity

theorem Zad1b : Tendsto (fun n x => cos (x / n)) atTop (𝓝 1) ∧
    ¬TendstoUniformly (fun n x => cos (x / n)) 1 atTop := by
  and_intros
  · rw [tendsto_pi_nhds]; intro x
    exact (continuous_cos.tendsto' _ _ cos_zero).comp (tendsto_const_div_atTop x)
  rw [Metric.tendstoUniformly_iff]; push Not; use 1, one_pos
  apply Eventually.frequently; filter_upwards [eventually_gt_atTop 0]; intro n hn
  use π * n; simp [hn.ne', dist_eq]; norm_num

theorem Zad1c : Tendsto (fun n x => arctan (n * x)) atTop (𝓝 ((π / 2) • sign)) ∧
    ¬TendstoUniformly (fun n x => arctan (n * x)) ((π / 2) • sign) atTop := by
  and_intros
  · simp only [tendsto_pi_nhds, Pi.smul_apply, smul_eq_mul]; intro x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [sign_of_neg hx, mul_neg, mul_one]; simp_rw [mul_comm]
      exact tendsto_nhds_of_tendsto_nhdsWithin
        (tendsto_arctan_atBot.comp (tendsto_const_mul_atTop_of_neg hx))
    · simp
    · rw [sign_of_pos hx, mul_one]; simp_rw [mul_comm]
      exact tendsto_nhds_of_tendsto_nhdsWithin
        (tendsto_arctan_atTop.comp (tendsto_const_mul_atTop hx))
  apply mt TendstoUniformly.continuous; rw [Classical.not_imp]
  use Frequently.of_forall (by fun_prop)
  apply mt (Continuous.continuousAt (x := 0))
  apply not_continuousAt_of_tendsto (l₁ := 𝓝[>] 0) (l₂ := 𝓝 (π / 2))
  · exact tendsto_nhdsWithin_congr (by simp +contextual [sign_of_pos]) tendsto_const_nhds
  · exact nhdsWithin_le_nhds
  · simp; positivity

theorem Zad1d (ha : a < 0) :
    TendstoUniformlyOn (fun n x => arctan (n * x)) (fun _ => -(π / 2)) atTop (Set.Iic a) := by
  rw [Metric.tendstoUniformlyOn_iff]; intro e he; simp only [Set.mem_Iic]
  wlog he' : e < π generalizing e
  · specialize this (π / 2) pi_div_two_pos (by simp [pi_pos])
    peel this; grw [this]; simp at he'; grw [he']; simpa
  filter_upwards [eventually_gt_atTop (tan (e + -(π / 2)) / a), eventually_gt_atTop 0]
  intro n hn hn' x hx
  rw [dist_eq, abs_lt]; and_intros; swap
  · grw [he]; simp [neg_pi_div_two_lt_arctan]
  grw [neg_lt_sub_iff_lt_add, ← strictMonoOn_tan.lt_iff_lt (arctan_mem_Ioo _) (by simp_all),
    tan_arctan, hx, ← div_lt_iff_of_neg ha]; assumption

theorem Zad2 : SummableUniformlyOn (fun (n : ℕ) x => x ^ 2 * exp (-n ^ 2 * x)) (Set.Ici 0) := by
  rw [summableUniformlyOn_iff_hasSumUniformlyOn]
  apply HasSumUniformlyOn.of_norm_le_summable_eventually (u := fun n : ℕ => 4 * exp (-2) / n ^ 4)
  · apply Summable.const_div; simp
  filter_upwards [eventually_cofinite_ne 0] with n hn
  simp only [neg_mul, norm_mul, norm_pow, norm_eq_abs, sq_abs, abs_exp]
  suffices IsMaxOn (fun x => x ^ 2 * rexp (-(↑n ^ 2 * x))) (Set.Ici 0) (2 / n ^ 2) by
    rw [isMaxOn_iff] at this; convert! this using 3; grind
  apply isMaxOn_Ici_of_deriv <;> try fun_prop
  · simp_rw [Set.mem_Ioo, and_imp]; intro x hl hu
    rw [deriv_fun_mul, deriv_pow_field, _root_.deriv_exp] <;> try fun_prop
    simp; field_simp; grw [hu]; simp_all
  · simp_rw [Set.mem_Ioi]; intro x hx; have hx' : 0 < x := by grw [← hx]; positivity
    rw [deriv_fun_mul, deriv_pow_field, _root_.deriv_exp] <;> try fun_prop
    simp; field_simp; grw [← hx]; simp_all

lemma _root_.iff_mem_Ioo_cases [LinearOrder α] {p : α → Prop} (hin : x ∈ Set.Ioo a b → p x)
    (hout : x ∉ Set.Icc a b → ¬p x) (ha : ¬p a) (hb : ¬p b) : (p x ↔ x ∈ Set.Ioo a b) := by grind

lemma _root_.iff_mem_Ico_cases [LinearOrder α] {p : α → Prop} (hin : x ∈ Set.Ioo a b → p x)
    (hout : x ∉ Set.Icc a b → ¬p x) (ha : p a) (hb : ¬p b) : (p x ↔ x ∈ Set.Ico a b) := by grind

theorem Zad3a : Summable (fun (n : ℕ) => (2 : ℝ) ^ (log n) ^ 2 * (x - 3) ^ n) (conditional ℕ)
    ↔ x ∈ Set.Ioo 2 4 := by
  have : Tendsto (fun (n : ℕ) => |(2 : ℝ) ^ (log n) ^ 2| ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simp [abs_rpow_of_nonneg, ← rpow_mul]; apply Tendsto.const_rpow_zero ?_ two_ne_zero
    apply squeeze_zero (by bound) (fun n => by grw [log_natCast_le_rpow_div n (inv_pos_of_pos three_pos)])
    apply ((tendsto_rpow_neg_atTop (inv_pos_of_pos three_pos)).const_mul_zero 9).natCast_atTop.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn; field_simp; norm_num [mul_assoc]
    rw [← rpow_add_one (by simpa), ← rpow_two, ← rpow_mul (by simp)]; congr; norm_num
  apply iff_mem_Ioo_cases (x := x)
    (fun hx => (summable_powerSeries_of_norm_lt_inv (by simpa) (by simp; grind)).to_conditional)
    (fun hx => not_summable_powerSeries_of_norm_gt_inv (by simpa) one_ne_zero (by simp; grind))
  · apply mt fun h => h.tendsto_atTop_zero'.comp (tendsto_const_mul_atTop' two_pos)
    apply not_tendsto_nhds_of_tendsto_atTop; norm_num [Function.comp_def]
    exact ((tendsto_natCast_atTop.const_mul_atTop' two_pos).log_atTop.atTop_pow₀ 2).const_rpow_atTop one_lt_two
  · apply mt Summable.tendsto_atTop_zero'; apply not_tendsto_nhds_of_tendsto_atTop
    norm_num; exact (tendsto_natCast_atTop.log_atTop.atTop_pow₀ 2).const_rpow_atTop one_lt_two

theorem Zad3b {x : ℝ} :
    Summable (fun (n : ℕ) => (n + 7) * (x + 3) ^ n / ((n ^ 2 + 1) * 9 ^ n)) (conditional ℕ)
    ↔ x ∈ Set.Ico (-12) 6 := by
  simp_rw [mul_div_right_comm]
  have : Tendsto (fun (n : ℕ) => (n + 7 : ℝ) / ((n ^ 2 + 1) * 9 ^ n)
      / ((n + 1 + 7) / (((n + 1) ^ 2 + 1) * 9 ^ (n + 1)))) atTop (𝓝 9) := by
    simp_rw [pow_succ]; field_simp; simp_rw [mul_div_right_comm _ (9 : ℝ)]; apply Tendsto.one_mul_const
    simp_rw [← div_div, mul_comm, div_div, mul_div_mul_comm]; apply Tendsto.mul_one; swap
    · convert (tendsto_natCast_add_atTop (8 : ℝ)).inv_atTop.const_sub_zero 1 using 2; field
    have X := tendsto_natCast_atTop (R := ℝ)
    convert (((X.atTop_mul_atTop₀ X).atTop_add_const 1).inv_atTop).const_add_zero 1
      |>.add_zero ((X.atTop_add X.inv_atTop).const_div_atTop 2) using 2; field
  apply iff_mem_Ico_cases (x := x)
    (fun hx => (summable_powerSeries_of_norm_lt_of_tendsto (by simpa (maxDischargeDepth := 3)
      [abs_of_nonneg, add_nonneg, sq_nonneg]) (by simp; grind)).to_conditional)
    (fun hx => not_summable_powerSeries_of_norm_gt_of_tendsto (by simpa (maxDischargeDepth := 3)
      [abs_of_nonneg, add_nonneg, sq_nonneg]) (by filter_upwards with n; positivity) (by simp; grind))
  · norm_num [← div_div, mul_comm_div, ← div_pow, mul_div_left_comm]
    apply summable_alternating_of_antitone_tendsto_zero
      (antitone_nat_of_succ_le fun n => by field_simp; norm_cast; ring_nf; bound)
    apply squeeze_zero' (by filter_upwards; bound)
    · filter_upwards [eventually_ne_atTop 0] with n hn using
        div_le_div_of_nonneg_left (by bound) (by positivity) (le_add_of_nonneg_right zero_le_one)
    simp_rw [sq, add_div, div_self_mul_self', ← sq]
    exact (tendsto_inv_atTop_zero.zero_add ((tendsto_pow_atTop two_ne_zero).const_div_atTop 7)).natCast_atTop
  · norm_num [← div_div]; rw [← summable_iff_conditional_of_nonneg (by bound)]
    apply mt (Summable.of_nonneg_of_le (show ∀ (n : ℕ), 0 ≤ (n + 7 : ℝ) / (n + 7) ^ 2 by bound)
      fun n => by field_simp; ring_nf; bound)
    simp_rw [sq, div_self_mul_self']; norm_cast
    exact mt (Summable.comp_nat_add (f := fun n => _⁻¹)) not_summable_natCast_inv

theorem Zad3c (x : ℝ) :
    Summable fun (n : ℕ) => (-1) ^ n * (x ^ (2 * n + 1) / ((2 * n + 1) * (2 * n + 1).factorial)) := by
  by_cases hx : x = 0
  · subst hx; simp
  let cx := ⌈|x|⌉₊
  apply summable_of_ratio_norm_eventually_le (r := (cx / (2 * cx + 3)) ^ 2)
  · rw [sq_lt_one_iff₀] <;> bound
  · simp (maxDischargeDepth := 4) [abs_of_nonneg, add_nonneg, mul_add, Nat.factorial_succ, pow_succ]
    field_simp; use cx; intro n hn; calc
    |x| ^ 2 * (2 * n + 1) * (2 * cx + 3) ^ 2
    _ ≤ cx ^ 2 * (2 * n + 2) * (2 * n + 3) ^ 2 := by gcongr; apply Nat.le_ceil; norm_num
    _ = (2 * (n + 1) + 1) ^ 2 * (2 * n + 1 + 1) * cx ^ 2 := by ring

/-
theorem Zad3d {x : ℝ} :
    Summable (fun (n : ℕ) => ((5 + (-1) ^ (n + 1)) / (9 + 3 * (-1) ^ n)) ^ n * (1 + x) ^ (3 * n)) (conditional ℕ)
    ↔ x ∈ Set.Ioo (-2) 0 := by
  rw [calc x ∈ Set.Ioo (-2) 0
    _ ↔ |1 + x| < 1 := by grind
    _ ↔ |(1 + x) ^ 3| < 1 := by simp [pow_lt_one_iff_of_nonneg]
    _ ↔ (1 + x) ^ 3 ∈ Set.Ioo (-1) 1 := by rw [abs_lt, Set.mem_Ioo]
  ]
  simp_rw [pow_mul]
  apply iff_mem_Ioo_cases (p := fun y => Summable (fun n => ((5 + _ ^ (n + 1)) / (9 + 3 * _ ^ n)) ^ n * y ^ n) _)
  · sorry
  · sorry
  all_goals
    apply mt (fun h => h.tendsto_atTop_zero'.comp ((tendsto_const_mul_atTop' two_pos).atTop_add_nat 1))
    norm_num [Function.comp_def, pow_succ]
-/
