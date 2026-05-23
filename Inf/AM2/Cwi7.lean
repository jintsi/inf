import Inf.AM1.Cwi4

open Real Topology Filter

namespace AM2.Zad7

theorem Zad1 : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => (2 * x ^ 2 - y ^ 2) / (x ^ 2 + 2 * y ^ 2))
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
