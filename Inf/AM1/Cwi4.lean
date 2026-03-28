import Inf.AM1.Cwi3
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.Complex.ExponentialBounds

open Real Topology Filter

/-- If two subsequences converge to different values, then a function/sequence does not converge.-/
theorem Filter.not_tendsto_nhds_of_seq {α : Type*} {β : Type*} {f : α → β} {k : Filter α} {g₁ g₂ : β}
    {x₁ x₂ : ℕ → α} [TopologicalSpace β] [T2Space β] [k.NeBot] : Tendsto x₁ atTop k → Tendsto x₂ atTop k →
    Tendsto (f ∘ x₁) atTop (𝓝 g₁) → Tendsto (f ∘ x₂) atTop (𝓝 g₂) → g₁ ≠ g₂ → ¬∃ g, Tendsto f k (𝓝 g) :=
  fun hx₁ hx₂ hfx₁ hfx₂ hg ⟨_, h⟩ => hg <|
    (tendsto_nhds_unique hfx₁ (h.comp hx₁)).trans (tendsto_nhds_unique (h.comp hx₂) hfx₂)

namespace AM1.Cwi4

theorem Zad1 : ¬∃ g, Tendsto (fun x => sin (x ^ 3)⁻¹) (𝓝[>] 0) (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := fun n => (n * π)⁻¹.cbrt) (x₂ := fun n => (π / 2 + n * (2 * π))⁻¹.cbrt)
  · simp_rw [cbrt, tendsto_nhdsWithin_iff, Set.mem_Ioi, eventually_atTop]; and_intros
    · convert (tendsto_const_div_pow π⁻¹ 1 (by simp)).rpow_const
        (Or.inr (show 0 ≤ 3⁻¹ by positivity)) using 2 <;> simp [div_eq_mul_inv]
    · exists 1; intro n hn; positivity
  · simp_rw [cbrt, tendsto_nhdsWithin_iff, Set.mem_Ioi, eventually_atTop]; and_intros
    · rw [← zero_rpow (show 3⁻¹ ≠ 0 by simp)]; apply Tendsto.rpow_const; swap; · simp
      exact tendsto_atTop_add_const_left _ _
        (tendsto_natCast_atTop_atTop.atTop_mul_const two_pi_pos) |>.inv_tendsto_atTop
    · exists 0; intro n _; positivity
  · simp only [Function.comp_def, cbrt, ← Real.rpow_ofNat]
    conv => arg 1; ext x; rw [Real.rpow_inv_rpow (by positivity) (by simp)]
    simp; rfl
  · simp only [Function.comp_def, cbrt, ← Real.rpow_ofNat]
    conv => arg 1; ext x; rw [Real.rpow_inv_rpow (by positivity) (by simp)]
    simp; rfl
  · exact zero_ne_one

theorem Zad2a : Tendsto (fun x => (√(5 - 2 * x) - √(3 - x)) / (x ^ 3 - 8)) (𝓝[≠] 2) (𝓝 (-24⁻¹)) := by
  apply Tendsto.congr' (f₁ := fun x => (-(x ^ 2 + 2 * x + 4) * (√(5 - 2 * x) + √(3 - x)))⁻¹)
  · rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1 / 2; simp only [dist_eq, mul_inv]; grind
  have hx : Tendsto (fun x : ℝ => x) (𝓝[≠] 2) (𝓝 2) := tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  convert ((((hx.pow 2).add (hx.const_mul 2)).add_const 4).neg.mul
    (((hx.const_mul 2).const_sub 5).sqrt.add (hx.const_sub 3).sqrt)).inv₀ (by norm_num) using 2
  norm_num

theorem Zad2b : Tendsto (fun x => √(x ^ 2 + π * x) + x) atBot (𝓝 (-π / 2)) := by
  simp_rw [← Filter.tendsto_comp_neg_atTop_iff, neg_sq, mul_neg, ← sub_eq_add_neg]
  apply Tendsto.congr' (f₁ := fun x => -π / (√(1 - π * x⁻¹) + 1))
  · rw [EventuallyEq, eventually_atTop]; use π; intro x hx; have xpos := pi_pos.trans_le hx
    field_simp; rw [sqrt_div' _ xpos.le, sqrt_mul xpos.le]; ring_nf
    rw [mul_comm x, mul_assoc, ← div_eq_mul_inv, Real.div_sqrt, sub_add_cancel,
      mul_inv_cancel_right₀ (sqrt_ne_zero'.mpr xpos), sq_sqrt, neg_add_cancel_comm_assoc]
    linarith
  convert (((tendsto_inv_atTop_zero.const_mul π).const_sub 1).sqrt.add_const 1).inv₀ (by simp)
    |>.const_mul (-π) using 2; simp; ring

theorem Zad2c : Tendsto (fun x => (sin x + cos x) / cos (2 * x)) (𝓝[≠] (-(π / 4))) (𝓝 (√2 / 2)) := by
  apply Tendsto.congr' (f₁ := fun x => 1 / (cos x - sin x))
  · rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]; use π / 4, by simp [pi_pos]
    simp_rw [dist_eq, sub_neg_eq_add, cos_two_mul', sq_sub_sq, add_comm, ← div_div]
    intro x hd hne; rw [div_self]
    rw [Ne, add_eq_zero_iff_eq_neg, ← cos_add_pi_div_two, ← Ne, ← sub_ne_zero, cos_sub_cos]
    simp_all; and_intros <;> rw [sin_eq_zero_iff_of_lt_of_lt] <;> grind
  apply tendsto_nhdsWithin_of_tendsto_nhds
  convert ((continuous_cos.sub continuous_sin).tendsto (-(π / 4))).inv₀ ?_ using 2 <;> simp
  exact sqrt_div_self

theorem Zad4 [Field α] [LinearOrder α] [IsStrictOrderedRing α] [TopologicalSpace α] [OrderTopology α]
    (f : α → α) (m k : α) : Tendsto (fun x => f x - (m * x + k)) atTop (𝓝 0) ↔
    Tendsto (fun x => f x / x) atTop (𝓝 m) ∧ Tendsto (fun x => f x - m * x) atTop (𝓝 k) := by
  constructor
  · intro h
    apply Tendsto.add_const k at h; simp_rw [zero_add, ← sub_sub, sub_add_cancel] at h
    simp only [h, and_true]
    replace h := (h.div_atTop tendsto_id).add_const m; rw [zero_add] at h
    apply h.congr'; rw [EventuallyEq, eventually_atTop]; use 1; grind
  · intro ⟨_, h⟩; convert h.sub_const k using 2 <;> simp [sub_sub]

open Classical in
theorem Zad8 {x : ℝ} : ContinuousAt (fun x => if Irrational x then 0 else x ^ 2) x ↔ x = 0 := by
  constructor; swap
  · intro h; subst h; simp [Metric.continuousAt_iff]
    intro e he; exists sqrt e, (by simpa); intro x hb
    split <;> simpa [sq_lt, ← abs_lt]
  intro h
  have h1 : Tendsto (fun x => if Irrational x then 0 else x ^ 2) (𝓝[{y | ¬Irrational y}] x) (𝓝 (x ^ 2)) := by
    refine tendsto_nhdsWithin_congr ?_ (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow 2))
    simp; tauto
  have h2 : Tendsto (fun x => if Irrational x then 0 else x ^ 2) (𝓝[{y | Irrational y}] x) (𝓝 0) := by
    refine tendsto_nhdsWithin_congr ?_ tendsto_const_nhds
    simp; tauto
  replace h1 := tendsto_nhds_unique' ?_ h1 (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto)
  replace h2 := tendsto_nhds_unique' ?_ h2 (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto)
  · exact sq_eq_zero_iff.mp (h1.trans h2.symm)
  · convert dense_irrational.denseRange_val.nhdsWithin_neBot x; simp
  · convert Rat.denseRange_cast.nhdsWithin_neBot x; simp [Irrational, Set.range]

theorem Zad9 : ∃ x ∈ Set.Ioo 0 1, exp (-x) = sin (π * x / 2) := by
  have h := intermediate_value_Ioo' zero_le_one ((Continuous.rexp continuous_neg).sub
    (Real.continuous_sin.comp' ((continuous_const_mul π).div_const 2))).continuousOn
  simp [Set.subset_def] at h
  convert h 0 (by grw [exp_neg_one_lt_half]; norm_num) zero_lt_one using 3
  exact sub_eq_zero.symm

theorem Zad11 : UniformContinuous NNReal.sqrt ∧ ¬∃ K, LipschitzWith K NNReal.sqrt := by
  and_intros
  · simp [Metric.uniformContinuous_iff, NNReal.dist_eq]
    intro e he; exists e ^ 2, sq_pos_of_pos he
    intro ⟨a, ha⟩ ⟨b, hb⟩ h; simp_rw [NNReal.coe_mk] at *
    wlog hab : b ≤ a generalizing a b
    · rw [abs_sub_comm]; rw [abs_sub_comm] at h; exact this b hb a ha h (le_of_not_ge hab)
    rw [← abs_of_pos he, ← sq_lt_sq]; apply h.trans_le'
    rw [sub_sq, sq_sqrt ha, sq_sqrt hb, abs_of_nonneg (sub_nonneg_of_le hab)]
    grw [← Real.sqrt_le_sqrt hab]; simp [mul_assoc, hb]; ring_nf; trivial
  · simp_rw [lipschitzWith_iff_dist_le_mul, not_exists, not_forall, not_le, NNReal.dist_eq]
    intro K; exists 0; norm_num
    by_cases hK : K = 0
    · exists 1; subst K; simp
    · exists 1 / (2 * K) ^ 2; simp; field_simp; simp
