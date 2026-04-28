import Inf.AM1.Tendsto
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.Peel

open Real Topology Filter

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
