import Inf.AM1.Cwi4

open Real Topology Filter

namespace AM2.Zad7

theorem Zad1a : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => (2 * x ^ 2 - y ^ 2) / (x ^ 2 + 2 * y ^ 2))
    (𝓝 (0, 0)) (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := fun n => ((1 / n, 0) : ℝ × ℝ)) (x₂ := fun n => ((0, 1 / n) : ℝ × ℝ))
  · simp [Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]
  · simp [Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]
  all_goals try
    simp [Function.comp_def]
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    ring_nf; simp +contextual [Nat.one_le_iff_ne_zero]
    intro i hi; rfl
  norm_num

theorem Zad1b : Tendsto (fun (x, y) => ((x - 1) ^ 2 + y ^ 2) / (√((x - 1) ^ 2 + y ^ 2 + 4) - 2))
    (𝓝[≠] (1, 0)) (𝓝 4) := by
  apply Tendsto.congr' (f₁ := fun (x, y) => √((x - 1) ^ 2 + y ^ 2 + 4) + 2)
  · filter_upwards [eventually_mem_nhdsWithin]; simp [-not_and]
    intro x y h; rw [eq_div_iff, ← sq_sub_sq, sq_sqrt]
    · ring
    · nlinarith
    · norm_num [sub_eq_zero, sqrt_eq_iff_mul_self_eq_of_pos]
      apply ne_of_gt; rw [not_and_or] at h
      cases h; rw [add_comm]
      all_goals apply lt_add_of_le_of_pos <;> simp_all [sq_nonneg, sq_pos_iff, sub_eq_zero]
  apply tendsto_nhdsWithin_of_tendsto_nhds; convert Continuous.tendsto ?_ ?_
  · norm_num; rw [show √4 = 2 by norm_num [sqrt_eq_iff_mul_self_eq_of_pos]]; norm_num
  · fun_prop

theorem Zad1c : Tendsto (fun (x, y) => arccos ((y * x ^ 2) / (x ^ 2 + y ^ 2))) (𝓝[≠] (0, 0))
    (𝓝 (π / 2)) := by
  simp [← arccos_zero]; apply Tendsto.comp (continuous_arccos.tendsto 0)
  rw [tendsto_zero_iff_abs_tendsto_zero]; apply Tendsto.squeeze (g := 0) (h := fun (x, y) => |y|)
  · exact tendsto_const_nhds
  · apply tendsto_nhdsWithin_of_tendsto_nhds; convert Continuous.tendsto ?_ ?_; simp; fun_prop
  · intro (x, y); simp
  · intro (x, y); dsimp; by_cases! h : x = 0
    · subst h; simp
    · simp [abs_div]; rw [abs_of_nonneg (a := _ + _)]
      · rw [div_le_iff₀]; rw [mul_add, le_add_iff_nonneg_right]
        · apply mul_nonneg <;> simp [sq_nonneg]
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg y)
      · exact add_nonneg (sq_nonneg x) (sq_nonneg y)

theorem Zad1d : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => (x * y ^ 2) / (x ^ 2 - y ^ 4)) (𝓝 (0, 0))
    (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := fun n => ((2 / n ^ 2, 1 / n) : ℝ × ℝ))
      (x₂ := fun n => ((-2 / n ^ 2, 1 / n) : ℝ × ℝ))
  · simp [Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]
    exact (tendsto_natCast_atTop.atTop_pow₀ 2).const_div_atTop 2
  · simp [Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]
    exact (tendsto_natCast_atTop.atTop_pow₀ 2).const_div_atTop (-2)
  all_goals try
    simp [Function.comp_def]
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    ring_nf; simp +contextual [Nat.one_le_iff_ne_zero]
    intro i hi; rfl
  norm_num
