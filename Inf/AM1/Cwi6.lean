import Inf.AM1.Deriv
import Inf.AM1.Continuous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace AM1.Cwi6

open Real

theorem Zad1a (x y : ℝ) : |cos x - cos y| ≤ |x - y| := by
  wlog h : y ≤ x
  · convert this y x (le_of_not_ge h) using 1 <;> rw [abs_sub_comm]
  rw [abs_of_nonneg (sub_nonneg_of_le h), abs_le, neg_eq_neg_one_mul]; and_intros
  · apply mul_sub_le_image_sub_of_le_deriv <;> simp [h, sin_le_one]
  · rw [← one_mul (x - y)]
    apply image_sub_le_mul_sub_of_deriv_le <;> simp [h, neg_le, neg_one_le_sin]

theorem Zad1b (hx : -1 < x) : x / (1 + x) ≤ log (1 + x) ∧ log (1 + x) ≤ x := by
  rw [neg_lt_iff_pos_add'] at hx
  rcases le_total 1 (1 + x) with hx' | hx' <;> and_intros
  · convert Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 1 (1 + x)) ?_ ?_ ?_
        1 ⟨le_rfl, hx'⟩ (1 + x) ⟨hx', le_rfl⟩ hx' using 1
    · simp [div_eq_mul_inv, mul_comm]; left; rfl
    · exact (log_one ▸ sub_zero _).symm
    · apply continuousOn_log.mono; simp
    · apply differentiableOn_log.mono; simp
    · simp; intros; field_simp; order
  · convert Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 1 (1 + x)) ?_ ?_ ?_
        1 ⟨le_rfl, hx'⟩ (1 + x) ⟨hx', le_rfl⟩ hx' using 1
    · exact (log_one ▸ sub_zero _).symm
    · simp; exact (one_mul x).symm
    · apply continuousOn_log.mono; simp
    · apply differentiableOn_log.mono; simp
    · simp; intros; field_simp; order
  · rw [← neg_le_neg_iff, ← zero_sub, ← log_one, neg_div', ← sub_add_cancel_left 1, div_eq_inv_mul]
    apply Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc (1 + x) 1) ?_ ?_ ?_
        (1 + x) ⟨le_rfl, hx'⟩ 1 ⟨hx', le_rfl⟩ hx'
    · apply continuousOn_log.mono; simpa
    · apply differentiableOn_log.mono; simp [hx.le]
    · simp; intro c hl hu; exact inv_anti₀ hx hl.le
  · rw [← neg_le_neg_iff, ← zero_sub (log _), ← log_one, ← sub_add_cancel_left 1, ← one_mul (_ - _)]
    apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (1 + x) 1) ?_ ?_ ?_
        (1 + x) ⟨le_rfl, hx'⟩ 1 ⟨hx', le_rfl⟩ hx'
    · apply continuousOn_log.mono; simpa
    · apply differentiableOn_log.mono; simp [hx.le]
    · simp; intro c hl hu; exact Bound.one_le_inv₀ (hx.trans hl) hu.le

theorem Zad2 : UniformContinuous arctan := by
  apply LipschitzWith.uniformContinuous
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_arctan
  intro x; simp; apply inv_le_one_of_one_le₀
  rw [nnnorm_of_nonneg (by positivity), ← NNReal.one_le_coe, NNReal.coe_mk]
  simp [sq_nonneg]

theorem Zad4 {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hb : ∃ c, ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ c) : UniformContinuousOn f (Set.Ioo a b) := by
  obtain ⟨c, hb⟩ := hb
  have hc : 0 ≤ c :=
    (abs_nonneg _).trans (hb ((a + b) / 2) ⟨left_lt_add_div_two.mpr hab, add_div_two_lt_right.mpr hab⟩)
  apply LipschitzOnWith.uniformContinuousOn (K := ⟨c, hc⟩)
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx; exact hd.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  · exact hb
  · exact convex_Ioo a b

theorem Zad6a : HasLimAt (fun x => (arcsin (3 * x) - 3 * arcsin x) / x ^ 3) Set.univ 0 4 := by
  apply deriv.lhopital_zero_hasLimAt
  · exists (1 / 3), (by simp); simp [abs_lt]; intro x hn hl hu
    exact ((differentiableAt_arcsin.mpr (by grind)).fun_comp' x (differentiableAt_fun_id.const_mul 3)).fun_sub
     ((differentiableAt_arcsin.mpr (by grind)).const_mul 3)
  · exists 1, zero_lt_one; simp; tauto
  · convert Continuous.hasLimAt ?_ 0; simp
    exact (continuous_const_mul 3).arcsin.sub (continuous_arcsin.const_mul 3)
  · convert Continuous.hasLimAt (continuous_pow 3) 0; simp
  apply HasLimAt.of_eventually_eq (a := 0) ⟨(1 / 3), by simp, by
    simp; intro x hx hb
    have := (differentiableAt_arcsin.mpr (by grind)).fun_comp' x (differentiableAt_fun_id.const_mul 3)
    have := (differentiableAt_arcsin.mpr (by grind)).const_mul (x := x) 3
    simp [*, deriv_comp_mul_left, ← mul_sub, mul_div_mul_left]
    rewrite [← mul_div_mul_left (c := (√(1 - (3 * x) ^ 2))⁻¹ + (√(1 - x ^ 2))⁻¹), ← sq_sub_sq,
      inv_pow, inv_pow, sq_sqrt (by simp; linarith), sq_sqrt (by simp; linarith)]; swap
    · apply ne_of_gt; apply add_pos_of_pos_of_nonneg <;> simp; linarith
    rw [inv_sub_inv, sub_sub_sub_cancel_left, mul_pow, ← sub_one_mul, div_div, ← mul_assoc, mul_div_mul_right]
    simpa; all_goals simp [sub_eq_zero]; apply Ne.symm; simp; grind
  ⟩; norm_num
  convert continuousAt_iff_hasLimAt.mp ?_
  · simp; norm_num; rfl
  refine ((ContinuousAt.mul ?h9 ?h1).mul (((?h9).sqrt.inv₀ ?_).add ((?h1).sqrt.inv₀ ?_))).const_div 8 ?_
    <;> try simp
  all_goals apply ContinuousAt.const_sub; (try apply ContinuousAt.const_mul); apply continuousAt_pow

/- TODO: de l'H for inf/inf
theorem Zad6b : HasRightLim (fun x => x ^ (1 / log (exp x - 1))) Set.univ 0 (exp 1) := by
  apply HasLimAt.of_eventually_eq (a := 0) ⟨1, zero_lt_one, by
    simp; intro x hp hx hb; rw [rpow_def_of_pos hp, ← div_eq_mul_inv]⟩
  apply HasLimAt.comp_continuous continuous_exp
  apply deriv.lhopital_zero_hasRightLim
  · exact ⟨1, zero_lt_one, fun x hp hx hb => differentiableAt_log hx⟩
  · exists 1, zero_lt_one; intro x hp hx hb; rw [deriv.log] <;> simp [sub_eq_zero, *]
  · sorry
  · sorry
  apply HasLimAt.of_eq (by
    simp; intro x hp hx; rewrite [deriv.log, inv_div_comm] <;> simp [sub_eq_zero, *, div_div]; rfl)
  apply deriv.lhopital_zero_hasRightLim (eventually_true _)
    <;> try simp [← mul_add_one, div_mul_cancel_left₀]
  · exists 1; grind
  · convert ((continuous_exp.sub_const 1).hasLimAt 0).subset (Set.subset_univ _); simp
  · convert ((continuous_exp.mul continuous_id').hasLimAt 0).subset (Set.subset_univ _) using 1; simp
  · convert continuousWithinAt_iff_hasLimAt.mp ((continuousWithinAt_id.add_const 1).inv₀ _) <;> simp
-/
