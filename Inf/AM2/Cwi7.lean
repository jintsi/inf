import Inf.AM1.Cwi4

open Real Topology Filter

namespace AM2.Zad7

theorem Zad1a : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => (2 * x ^ 2 - y ^ 2) / (x ^ 2 + 2 * y ^ 2))
    (𝓝[≠] (0, 0)) (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := fun n => ((1 / n, 0) : ℝ × ℝ)) (x₂ := fun n => ((0, 1 / n) : ℝ × ℝ))
  any_goals
    simp [tendsto_nhdsWithin_iff, Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]; use 1; bound
  all_goals try
    simp [Function.comp_def]
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    ring_nf; simp +contextual [Nat.one_le_iff_ne_zero]
    intro i hi; rfl
  norm_num

theorem Zad1b : Tendsto (fun (x, y) => ((x - 1) ^ 2 + y ^ 2) / (√((x - 1) ^ 2 + y ^ 2 + 4) - 2))
    (𝓝[≠] (1, 0)) (𝓝 4) := by
  apply Tendsto.congr' (f₁ := fun (x, y) => √((x - 1) ^ 2 + y ^ 2 + 4) + 2)
  · filter_upwards [eventually_mem_nhdsWithin]; simp [-not_and, not_and_or]
    intro x y h; rw [eq_div_iff, ← sq_sub_sq, sq_sqrt]
    · ring
    · positivity
    · norm_num [sub_eq_zero, sqrt_eq_iff_mul_self_eq_of_pos]; cases h <;> positivity
  apply tendsto_nhdsWithin_of_tendsto_nhds; apply Continuous.tendsto' (by fun_prop)
  · norm_num; rw [show √4 = 2 by norm_num [sqrt_eq_iff_mul_self_eq_of_pos]]; norm_num

theorem Zad1c : Tendsto (fun (x, y) => arccos ((y * x ^ 2) / (x ^ 2 + y ^ 2))) (𝓝 (0, 0))
    (𝓝 (π / 2)) := by
  simp [← arccos_zero]; apply Tendsto.comp (continuous_arccos.tendsto 0)
  rw [tendsto_zero_iff_abs_tendsto_zero]; apply tendsto_const_nhds.squeeze (h := fun (x, y) => |y|)
  · apply Continuous.tendsto' (by fun_prop); simp
  · intro (x, y); simp
  · intro (x, y); dsimp; by_cases! h : x = 0
    · subst h; simp
    · simp [abs_div]; rw [abs_of_nonneg (a := _ + _) (by positivity), div_le_iff₀ (by positivity),
        mul_add, le_add_iff_nonneg_right]; positivity

theorem Zad1d : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => (x * y ^ 2) / (x ^ 2 - y ^ 4)) (𝓝[≠] (0, 0))
    (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := fun n => ((2 / n ^ 2, 1 / n) : ℝ × ℝ))
      (x₂ := fun n => ((-2 / n ^ 2, 1 / n) : ℝ × ℝ))
  any_goals
    simp [tendsto_nhdsWithin_iff, Prod.tendsto_iff, tendsto_inv_atTop_nhds_zero_nat]; constructor
    · exact (tendsto_natCast_atTop.atTop_pow₀ 2).const_div_atTop _
    · use 1; bound
  any_goals
    simp [Function.comp_def]
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    ring_nf; simp +contextual [Nat.one_le_iff_ne_zero]
    intro i hi; rfl
  norm_num

/-- Half of **Jordan's inequality** for the absolute value of `arcsin`. -/
theorem _root_.Real.abs_arcsin_le_mul_abs (x : ℝ) : |arcsin x| ≤ π / 2 * |x| := by
  by_cases! hr : x ≤ 1
  by_cases! hl : -1 ≤ x
  any_goals
    trans π / 2; simp [abs_le, arcsin_le_pi_div_two, neg_pi_div_two_le_arcsin]
    apply le_mul_of_one_le_right pi_div_two_pos.le; grind
  wlog! h : 0 ≤ x
  · specialize this (-x) (neg_le_of_neg_le hl); simp_all [h.le]
  rw [abs_of_nonneg (arcsin_nonneg.mpr h), abs_of_nonneg h, arcsin_le_iff_le_sin ⟨hl, hr⟩]
  · exact le_sin_mul h hr
  constructor
  · rwa [neg_eq_neg_one_mul, mul_comm, mul_le_mul_iff_right₀ pi_div_two_pos]
  · rwa [mul_le_iff_le_one_right pi_div_two_pos]

theorem Zad1e : Tendsto (fun (x, y) => arcsin (3 * x * y) / √(x ^ 2 + y ^ 2)) (𝓝 (0, 0)) (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]; simp [Function.comp_def, abs_div, abs_of_nonneg]
  apply tendsto_const_nhds.squeeze (h := fun (x, y) => 3 * π / 2 * √(x ^ 2 + y ^ 2))
  · apply Continuous.tendsto' (by fun_prop); simp
  · intro (x, y); simp; positivity
  intro (x, y); simp; apply div_le_of_le_mul₀ (by positivity) (by positivity)
  grw [abs_arcsin_le_mul_abs, mul_assoc, abs_mul, abs_of_nonneg (by simp)]; field_simp
  grw [sq_sqrt (by positivity), abs_mul, ← sq_abs, ← sq_abs y]; nlinarith

theorem Zad1f : Tendsto (fun (x, y) => exp (-(x ^ 2 + y ^ 2)⁻¹) / (x ^ 4 + y ^ 4)) (𝓝 (0, 0)) (𝓝 0) := by
  convert Tendsto.piecewise (α := ℝ × ℝ) (s := {(0, 0)}) ?_ ?_
  · rw [Set.piecewise_same]
  · simp; convert tendsto_pure_nhds _ _; simp
  apply tendsto_const_nhds.squeeze (b := 𝓝[≠] (0, 0))
      (h := (fun s => 2 * s ^ 2 / exp s) ∘ (fun (x, y) => (x ^ 2 + y ^ 2)⁻¹))
  · apply Tendsto.comp (y := atTop)
    · convert tendsto_div_pow_mul_exp_add_atTop (1 / 2) 0 2 (by simp) using 2; ring
    apply Tendsto.inv_tendsto_nhdsGT_zero; apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply tendsto_nhdsWithin_of_tendsto_nhds; apply Continuous.tendsto' (by fun_prop); simp
    · filter_upwards [eventually_mem_nhdsWithin]; simp [-not_and, not_and_or]
      rintro x y (hx | hy) <;> positivity
  · intro (x, y); dsimp; positivity
  · intro (x, y); simp [Real.exp_neg]; by_cases! h : x ≠ 0 ∨ y ≠ 0
    · cases h; all_goals
        field_simp; ring_nf; grw [mul_right_comm, mul_comm _ 2, two_mul_le_add_pow_two]; ring_nf; trivial
    · rcases h with ⟨rfl, rfl⟩; simp

theorem Zad1g : Tendsto (fun ((x, y) : ℝ × ℝ) => (x + y) / (x ^ 2 - x * y + y ^ 2))
    (atTop ×ˢ atTop) (𝓝 0) := by
  apply tendsto_const_nhds.squeeze' (h := fun (x, y) => 2 / x + 2 / y)
  · exact (tendsto_fst.const_div_atTop 2).zero_add (tendsto_snd.const_div_atTop 2)
  · rw [prod_atTop_atTop_eq]; filter_upwards [eventually_ge_atTop (0, 0)]; simp; intro x y hx hy
    apply div_nonneg (by positivity); grw [sq_nonneg (x - y)]; nlinarith
  · filter_upwards [(eventually_gt_atTop 0).prod_inl _, (eventually_gt_atTop 0).prod_inr _]
      with ⟨x, y⟩ hx hy; dsimp at *
    have : 0 < x ^ 2 - x * y + y ^ 2 := by grw [sq_nonneg (x - y)]; nlinarith
    trans 2 * (x + y) / (x ^ 2 + y ^ 2)
    · field_simp at ⊢ this; ring_nf; grw [neg_add_eq_sub, sub_add_eq_add_sub, le_sub_iff_add_le,
        show x * y * 2 = 2 * x * y by ring, two_mul_le_add_sq]; linarith
    · field_simp; ring_nf; nlinarith

theorem Zad1h : Tendsto (fun ((x, y) : ℝ × ℝ) => (x ^ 2 * y ^ 2 / (x ^ 4 + y ^ 4)) ^ |x|⁻¹)
    (𝓝[≠] 0 ×ˢ atTop) (𝓝 0) := by
  apply tendsto_const_nhds.squeeze' (h := fun (x, y) => 2⁻¹ ^ |x|⁻¹)
  · apply Tendsto.comp (g := fun x => 2⁻¹ ^ |x|⁻¹) ?_ tendsto_fst
    apply tendsto_abs_nhdsNE_zero.inv_tendsto_nhdsGT_zero.const_rpow_atTop_of_lt_one <;> norm_num
  · filter_upwards with (x, y); positivity
  · filter_upwards [(eventually_gt_atTop 0).prod_inr _] with (x, y) hy; dsimp at *
    apply rpow_le_rpow <;> try positivity
    field_simp; convert two_mul_le_add_sq (x ^ 2) (y ^ 2) using 1 <;> ring

theorem Zad2a : Tendsto (fun x : ℝ => (𝓝 0).limUnder fun y : ℝ => x * y ^ 2 / (x ^ 2 + y ^ 4))
    (𝓝 0) (𝓝 0) := by
  convert tendsto_const_nhds using 2 with x; apply Tendsto.limUnder_eq
  by_cases! hx : x = 0
  · subst hx; simp
  apply Continuous.tendsto' (by fun_prop (disch := intro y; positivity)); simp

theorem Zad2b : Tendsto (fun y : ℝ => (𝓝 0).limUnder fun x : ℝ => x * y ^ 2 / (x ^ 2 + y ^ 4))
    (𝓝 0) (𝓝 0) := by
  convert tendsto_const_nhds using 2 with y; apply Tendsto.limUnder_eq
  by_cases! hy : y = 0
  · subst hy; simp
  apply Continuous.tendsto' (by fun_prop (disch := intro x; positivity)); simp

theorem Zad2c : ¬∃ g, Tendsto (fun ((x, y) : ℝ × ℝ) => x * y ^ 2 / (x ^ 2 + y ^ 4)) (𝓝[≠] (0, 0)) (𝓝 g) := by
  apply not_tendsto_nhds_of_seq (x₁ := (fun n => (1 / n ^ 2, 1 / n) : ℕ → ℝ × ℝ)) (x₂ := (fun n => (-1 / n ^ 2, 1 / n) : ℕ → ℝ × ℝ))
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; swap
    · simp; use 1; bound
    exact (tendsto_const_div_pow 1 2 two_ne_zero).prodMk_nhds tendsto_one_div_atTop_nhds_zero_nat
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; swap
    · simp; use 1; bound
    exact (tendsto_const_div_pow (-1) 2 two_ne_zero).prodMk_nhds tendsto_one_div_atTop_nhds_zero_nat
  · apply tendsto_atTop_of_eventually_const (i₀ := 1) (x := 2⁻¹); intro i hi; dsimp; field
  · apply tendsto_atTop_of_eventually_const (i₀ := 1) (x := -2⁻¹); intro i hi; dsimp; field
  · norm_num

theorem Zad3a : ¬Continuous fun ((x, y) : ℝ × ℝ) => (x * y ^ 3 - y * x ^ 3) / (x ^ 4 + y ^ 4) := by
  apply mt (Continuous.continuousAt (x := (0, 0)))
  apply not_continuousAt_of_tendsto (l₁ := atTop.map (fun n => (1 / (n + 1), 2 / (n + 1)) : ℕ → ℝ × ℝ))
  · simp [Function.comp_def]; field_simp; ring_nf; exact tendsto_const_nhds
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.prodMk_nhds ((tendsto_natCast_add_atTop 1).const_div_atTop 2)
  · norm_num

theorem Zad3b : Continuous fun ((x, y) : ℝ × ℝ) => x ^ 2 / (|x| + |y|) := by
  rw [continuous_iff_continuousAt]; intro (x, y)
  by_cases! h : (x, y) ≠ (0, 0)
  · simp [-not_and, not_and_or] at h; fun_prop (disch := cases h <;> positivity)
  simp at h; rcases h with ⟨rfl, rfl⟩; apply continuousAt_of_tendsto_nhds (y := 0)
  apply tendsto_const_nhds.squeeze (h := fun (x, y) => |x| + |y|)
  · apply Continuous.tendsto' (by fun_prop); simp
  · intro (x, y); positivity
  intro (x, y); dsimp; apply le_of_le_of_eq ?_ (mul_self_div_self _)
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  simp [mul_add, add_mul, sq, add_assoc]; rw [← sq]; positivity
