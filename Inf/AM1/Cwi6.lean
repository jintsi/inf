import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.LHopital

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
  have hc : 0 ≤ c := (abs_nonneg _).trans (hb ((a + b) / 2) (by grind))
  apply LipschitzOnWith.uniformContinuousOn (K := ⟨c, hc⟩)
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx; exact hd.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  · exact hb
  · exact convex_Ioo a b

open Topology Filter

theorem Zad6a : Tendsto (fun x => (arcsin (3 * x) - 3 * arcsin x) / x ^ 3) (𝓝[≠] 0) (𝓝 4) := by
  have h : ∀ᶠ x in 𝓝[≠] 0, (DifferentiableAt ℝ (fun x => arcsin (3 * x)) x ∧
      DifferentiableAt ℝ (fun x => 3 * arcsin x) x) := by
    apply eventually_nhdsWithin_of_eventually_nhds; simp_rw [Metric.eventually_nhds_iff, dist_eq]
    exists 1 / 3, (by simp); intro x hx; and_intros
    · exact (differentiableAt_arcsin.mpr (by grind)).fun_comp' x (by fun_prop)
    · exact (differentiableAt_arcsin.mpr (by grind)).const_mul 3
  apply deriv.lhopital_zero_nhdsNE
  · apply h.mono; simp +contextual
  · simpa using eventually_mem_nhdsWithin
  · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))
  · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))
  · apply Tendsto.congr' (f₁ := fun x => 8 / ((1 - 9 * x ^ 2) * (1 - x ^ 2) * (√(1 - 9 * x ^ 2)⁻¹ + √(1 - x ^ 2)⁻¹)))
    · apply h.mp; simp_rw [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff,
        Metric.eventually_nhds_iff, dist_eq, sub_zero]; simp +contextual [deriv_comp_mul_left]
      exists 1 / 3, (by simp); intro x hb hx _ _
      have : 0 < 1 - x ^ 2 := by simp; linarith
      have : 0 < 1 - (3 * x) ^ 2 := by simp; linarith
      ring_nf at this; field_simp; ring_nf; field_simp
      rw [sq_sqrt, sq_sqrt] <;> bound
    convert tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
    · norm_num
    · fun_prop (disch := positivity)
