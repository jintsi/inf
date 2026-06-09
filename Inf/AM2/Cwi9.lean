import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory intervalIntegral Real Topology Filter

@[fun_prop]
theorem intervalIntegral.continuous_parametric_intervalIntegral_of_continuous_of_continuous
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] {μ : Measure ℝ} [NoAtoms μ]
    [IsLocallyFiniteMeasure μ] {f : X → ℝ → E} {a b : X → ℝ} (hf : Continuous f.uncurry)
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x => ∫ (t : ℝ) in a x..b x, f x t ∂μ := by
  rw [continuous_congr fun x => ?_]; pick_goal 3
  · rw [← integral_interval_sub_left (a := 0)] <;> apply Continuous.intervalIntegrable <;> fun_prop
  fun_prop

theorem measurableSet_region_between_cc_of_continuousOn [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hs : MeasurableSet s) : MeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)} := by
  classical
  have hf' := hf.measurable_piecewise continuous_zero.continuousOn hs
  have hg' := hg.measurable_piecewise continuous_zero.continuousOn hs
  convert measurableSet_region_between_cc hf' hg' hs using 3 with p; simp +contextual

theorem integral_region_between_cc [MeasureSpace α] [SFinite (volume : Measure α)]
    [NormedAddCommGroup β] [NormedSpace ℝ β] {f g : α → ℝ} {F : α × ℝ → β} (hfg : ∀ x ∈ s, f x ≤ g x)
    (hs : MeasurableSet s) (hs' : MeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)})
    (hF : IntegrableOn F {p | p.1 ∈ s ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)}) :
    ∫ p in {p | p.1 ∈ s ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)}, F p = ∫ x in s, ∫ y in f x..g x, F (x, y) := calc
  ∫ p in {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}, F p
  _ = ∫ x, ∫ y, {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}.indicator F (x, y) := by
    rw [← MeasureTheory.integral_indicator hs', Measure.volume_eq_prod, integral_prod]
    rwa [integrable_indicator_iff hs', ← Measure.volume_eq_prod]
  _ = ∫ x in s, ∫ y, {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}.indicator F (x, y) := by
    symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; convert integral_zero ℝ β with y; simp [hx]
  _ = ∫ x in s, ∫ y in f x..g x, {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}.indicator F (x, y) := by
    apply setIntegral_congr_fun hs; intro x hx; dsimp
    rw [integral_of_le (hfg x hx), ← integral_Icc_eq_integral_Ioc]; symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero; simp +contextual
  _ = ∫ x in s, ∫ y in f x..g x, F (x, y) := by
    apply setIntegral_congr_fun hs; intro x hx; apply integral_congr; intro y hy; simp_all

/-- **Theorem 14.2**: A double integral on a normal domain is equal to a repeated integral. -/
theorem integral_normal_domain_cc {F : ℝ × ℝ → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) (hab : a ≤ b)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x)
    (hF : ContinuousOn F {p | (p.1 ∈ Set.Icc a b) ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)}) :
    ∫ p in {p | (p.1 ∈ Set.Icc a b) ∧ p.2 ∈ Set.Icc (f p.1) (g p.1)}, F p = ∫ x in a..b, ∫ y in f x..g x, F (x, y) := by
  rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hf' := (hf.measurable_piecewise continuous_zero.continuousOn measurableSet_Icc)
  have hg' := (hg.measurable_piecewise continuous_zero.continuousOn measurableSet_Icc)
  apply integral_region_between_cc hfg measurableSet_Icc
    (measurableSet_region_between_cc_of_continuousOn hf hg measurableSet_Icc)
  apply hF.integrableOn_compact; apply Metric.isCompact_of_isClosed_isBounded
  · convert! (isClosed_Icc.epigraph hf).inter (isClosed_Icc.hypograph hg) using 1
    ext p; simp +contextual [and_assoc]
  obtain ⟨bf, hbf⟩ := isCompact_Icc.bddBelow_image hf; simp [lowerBounds, -Set.mem_Icc] at hbf
  obtain ⟨bg, hbg⟩ := isCompact_Icc.bddAbove_image hg; simp [upperBounds, -Set.mem_Icc] at hbg
  apply Bornology.IsBounded.subset (t := Set.Icc a b ×ˢ Set.Icc bf bg)
  · simp [Metric.isBounded_Icc]
  intro (x, y); simp [-Set.mem_Icc]; intro hx; simp [hx.1, hx.2]; grw [hbf x hx, ← hbg x hx]; trivial

theorem integral_normal_domain_cc' {F : ℝ × ℝ → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) (hab : a ≤ b)
    (hfg : ∀ y ∈ Set.Icc a b, f y ≤ g y)
    (hF : ContinuousOn F {(x, y) | (y ∈ Set.Icc a b) ∧ x ∈ Set.Icc (f y) (g y)}) :
    ∫ p in {(x, y) | (y ∈ Set.Icc a b) ∧ x ∈ Set.Icc (f y) (g y)}, F p = ∫ y in a..b, ∫ x in f y..g y, F (x, y) := by
  trans ∫ p in {(y, x) | (y ∈ Set.Icc a b) ∧ x ∈ Set.Icc (f y) (g y)}, F p.swap
  · rw [← MeasureTheory.integral_indicator, Measure.volume_eq_prod, ← integral_prod_swap,
      ← MeasureTheory.integral_indicator]; rfl
    · exact measurableSet_region_between_cc_of_continuousOn hf hg measurableSet_Icc
    · rw [← measurableSet_swap_iff]
      exact measurableSet_region_between_cc_of_continuousOn hf hg measurableSet_Icc
  · apply integral_normal_domain_cc hf hg hab hfg
    apply ContinuousOn.image_comp_continuous ?_ continuous_swap
    simpa [Set.image_swap_eq_preimage_swap] using hF

theorem ContinuousLinearMap.det_dim2 [CommRing R] [TopologicalSpace R] (f : R × R →L[R] R × R) :
    f.det = (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2 := by
  simp [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd R),
    -LinearMap.det_toMatrix, Matrix.det_fin_two, LinearMap.toMatrix_apply]

namespace AM2.Cwi9

theorem Zad1a : ∫ p in {(x, y) | 3 * √x ≤ y ∧ y ≤ 4 - x ^ 2}, p.1 * p.2 = -15 / 4 := calc
  ∫ p in {(x, y) | 3 * √x ≤ y ∧ y ≤ 4 - x ^ 2}, p.1 * p.2
  _ = ∫ p in {(x, y) | (x ∈ Set.Icc (-2) 1) ∧ y ∈ Set.Icc (3 * √x) (4 - x ^ 2)}, p.1 * p.2 := by
    congr! with p; simp; intro h1 h2; and_intros
    · have h3 : 0 ≤ p.2 := by grw [← h1]; simp
      grw [← h3] at h2; simp at h2; nlinarith
    · have := h1.trans h2; contrapose! this -- grw sucks here
      apply (mul_lt_mul_of_pos_left (sqrt_lt_sqrt zero_le_one this) three_pos).trans_le'
      grw [← this]; norm_num
  _ = ∫ x in -2..1, ∫ y in 3 * √x..4 - x ^ 2, x * y := by
    refine integral_normal_domain_cc (f := fun x => 3 * √x) (g := fun x => 4 - x ^ 2)
      (by fun_prop) (by fun_prop) (by trans 0 <;> simp) ?_ (by fun_prop)
    intro x hx; by_cases! hx' : x < 0
    · simp_all [sqrt_eq_zero_of_nonpos hx'.le]; nlinarith
    trans 3
    · simp_all
    · norm_num [le_sub_comm]; simp_all [abs_of_nonneg]
  _ = (∫ x in -2..0, ∫ y in 3 * √x..4 - x ^ 2, x * y) + ∫ x in 0..1, ∫ y in 3 * √x..4 - x ^ 2, x * y := by
    symm; apply integral_add_adjacent_intervals <;> apply Continuous.intervalIntegrable <;> fun_prop
  _ = (∫ x in -2..0, x * (4 - x ^ 2) ^ 2 / 2) + ∫ x in 0..1, x * ((4 - x ^ 2) ^ 2 - 9 * x) / 2 := by
    congr 1; all_goals
      apply integral_congr; intro x hx; simp at hx; dsimp; rw [intervalIntegral.integral_const_mul]
    · simp [sqrt_eq_zero_of_nonpos hx.2, mul_div_assoc]
    · norm_num [mul_pow, hx.1, mul_div_assoc]
  _ = -15 / 4 := by ring_nf; simp (maxDischargeDepth := 4); norm_num

lemma Zad1b_cos_add_sin_pos (h : t ∈ Set.Icc (π / 4) (π / 2)) : 0 < cos t + sin t := by
  simp at h; apply add_pos_of_nonneg_of_pos
  · apply cos_nonneg_of_mem_Icc; simp_all; linarith
  · apply sin_pos_of_pos_of_lt_pi <;> linarith [pi_pos]

theorem Zad1b : ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y},
    1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) = 1 - π / 4 := calc
  ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}, 1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ)
  _ = ∫ p, {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}.indicator
      (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) p := by
    rw [MeasureTheory.integral_indicator]; simp; fun_prop
  _ = ∫ p in polarCoord.target, p.1 * {(x, y) | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}.indicator
      (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) (polarCoord.symm p) := by
    rw [← integral_comp_polarCoord_symm]; simp_rw [smul_eq_mul]
  _ = ∫ p in {(r, t) : ℝ × ℝ | t ∈ Set.Icc (π / 4) (π / 2) ∧ r ∈ Set.Icc (cos t + sin t)⁻¹ 1},
      p.1 * (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) (polarCoord.symm p) := by
    generalize (fun ((x, y) : ℝ × ℝ) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) = f
    rw [← MeasureTheory.integral_indicator (by exact measurableSet_Ioi.prod measurableSet_Ioo),
        ← MeasureTheory.integral_indicator (by simp; fun_prop)]
    congr; ext x; simp [Set.indicator, ← ite_and]; congr 1; simp [mul_pow, ← mul_add]; constructor
    · simp? +contextual [abs_of_pos] says
        simp +contextual only [and_imp, abs_of_pos, mul_le_mul_iff_right₀, and_true]
      intro hlr hlt hut hur h1 h2; constructor
      · grw [hur, one_mul] at h2; swap
        · exact nonneg_of_mul_nonneg_right (zero_le_one.trans h2) hlr
        by_contra! +distrib hut | hlt
        · by_cases! ht : 0 ≤ x.2
          · revert h1; simp; trans √2 / 2
            · rw [← sin_pi_div_four]; apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
            · rw [← cos_pi_div_four]; apply cos_lt_cos_of_nonneg_of_le_pi <;> linarith
          · revert h2; grw [cos_le_one]; simpa using sin_neg_of_neg_of_neg_pi_lt ht hlt
        · revert h2; grw [sin_le_one]; simpa using cos_neg_of_pi_div_two_lt_of_lt hlt (by linarith)
      · rwa [inv_le_iff_one_le_mul₀ (pos_of_mul_pos_right (one_pos.trans_le h2) hlr.le)]
    · simp [and_assoc]; intro hlt hut hlr hur
      have := Zad1b_cos_add_sin_pos ⟨hlt, hut⟩
      rw [and_iff_left_of_imp]
      · grw [← hlr]; rwa [inv_pos]
      intro hlr'; and_intros <;> try linarith [pi_pos]
      · simpa [abs_of_pos hlr']
      · simp [hlr']; trans √2 / 2
        · rw [← cos_pi_div_four]; apply cos_le_cos_of_nonneg_of_le_pi <;> linarith
        · rw [← sin_pi_div_four]; apply sin_le_sin_of_le_of_le_pi_div_two <;> linarith
      · rwa [← inv_le_iff_one_le_mul₀ this]
  _ = ∫ p in {(r, t) : ℝ × ℝ | t ∈ Set.Icc (π / 4) (π / 2) ∧ r ∈ Set.Icc (cos t + sin t)⁻¹ 1},
      p.1 ^ (-2 : ℤ) := by
    simp only [Set.mem_Icc, polarCoord_symm_apply, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one,
      one_div]; apply setIntegral_congr_fun (by simp; fun_prop); dsimp [Set.EqOn]
    intro x hx; rw [← rpow_natCast_mul]; norm_num; field; grw [← hx.2.1, inv_nonneg]
    exact (Zad1b_cos_add_sin_pos hx.1).le
  _ = ∫ t in π / 4..π / 2, ∫ r in (cos t + sin t)⁻¹..1, r ^ (-2 : ℤ) := by
    refine integral_normal_domain_cc' (f := fun t => (cos t + sin t)⁻¹) (g := fun _ => 1)
      (by fun_prop (disch := intro x hx; exact (Zad1b_cos_add_sin_pos hx).ne')) continuousOn_const
      (by linarith [pi_nonneg]) ?_ ?_; swap
    · apply ContinuousOn.zpow₀; fun_prop; intro x ⟨ht, hr⟩; left
      exact ((inv_pos.mpr (Zad1b_cos_add_sin_pos ht)).trans_le hr.1).ne'
    intro t ht; apply inv_le_one_of_one_le₀
    rw [← one_le_sq_iff₀ (Zad1b_cos_add_sin_pos ht).le, add_sq', cos_sq_add_sin_sq, mul_right_comm,
      ← sin_two_mul, le_add_iff_nonneg_right]; dsimp [Set.Icc] at ht
    apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
  _ = ∫ t in π / 4..π / 2, cos t + sin t - 1 := by
    apply integral_congr; intro t ht; dsimp; rw [integral_zpow]
    · simp; ring
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at ht
    simp; apply Set.notMem_uIcc_of_lt <;> simp [Zad1b_cos_add_sin_pos ht]
  _ = 1 - π / 4 := by simp; ring

theorem Zad1c : ∫ p in {(x, y) : ℝ × ℝ | y ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ 2 * y ∧ 0 ≤ x},
    p.1 * p.2 ^ 2 = 31 / 40 := calc
  ∫ p in {(x, y) : ℝ × ℝ | y ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ 2 * y ∧ 0 ≤ x}, p.1 * p.2 ^ 2
  _ = ∫ p, {(x, y) : ℝ × ℝ | y ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ 2 * y ∧ 0 ≤ x}.indicator
      (fun (x, y) => x * y ^ 2) p := by rw [MeasureTheory.integral_indicator]; simp; fun_prop
  _ = ∫ p in polarCoord.target, p.1 *
      {(x, y) : ℝ × ℝ | y ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ 2 * y ∧ 0 ≤ x}.indicator
      (fun (x, y) => x * y ^ 2) (polarCoord.symm p) := by
    rw [← integral_comp_polarCoord_symm]; simp_rw [smul_eq_mul]
  _ = ∫ p in {(r, t) | (t ∈ Set.Ioc 0 (π / 2)) ∧ r ∈ Set.Icc (sin t) (2 * sin t)},
      p.1 * (fun (x, y) => x * y ^ 2) (polarCoord.symm p) := by
    generalize (fun ((x, y) : ℝ × ℝ) => x * y ^ 2) = f
    rw [← MeasureTheory.integral_indicator (by exact measurableSet_Ioi.prod measurableSet_Ioo),
        ← MeasureTheory.integral_indicator (by simp; fun_prop)]
    congr; ext x; simp [Set.indicator, ← ite_and]; congr 1; simp [mul_pow, ← mul_add]; constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩; and_intros
      · contrapose! h5; apply (sq_pos_of_pos h1).trans_le'
        apply mul_nonpos_of_nonneg_of_nonpos zero_le_two
        apply mul_nonpos_of_nonneg_of_nonpos h1.le
        exact sin_nonpos_of_nonpos_of_neg_pi_le h5 h2.le
      · contrapose! h6; apply mul_neg_of_pos_of_neg h1
        apply cos_neg_of_pi_div_two_lt_of_lt h6; linarith
      · nlinarith
      · nlinarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; and_intros
      · apply h3.trans_lt'; apply sin_pos_of_pos_of_lt_pi h1; linarith
      · linarith
      · linarith
      · nlinarith
      · nlinarith
      · apply mul_nonneg; linarith
        exact cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h2
  _ = ∫ p in {(r, t) | (t ∈ Set.Icc 0 (π / 2)) ∧ r ∈ Set.Icc (sin t) (2 * sin t)},
      p.1 * (fun (x, y) => x * y ^ 2) (polarCoord.symm p) := by
    apply setIntegral_congr_set; symm; convert insert_ae_eq_self ((0, 0) : ℝ × ℝ) _; swap
    · infer_instance
    apply Set.ext; simp; intro r t; nth_rw 1 [le_iff_eq_or_lt']; simp [or_and_right]
    apply or_congr_left; constructor
    · simpa +contextual using fun _ _ => ge_antisymm
    · simpa +contextual using fun _ _ => pi_div_two_pos.le
  _ = ∫ p in {(r, t) | (t ∈ Set.Icc 0 (π / 2)) ∧ r ∈ Set.Icc (sin t) (2 * sin t)},
      p.1 ^ 4 * cos p.2 * sin p.2 ^ 2 := by simp; ring_nf
  _ = ∫ t in 0..π / 2, ∫ r in sin t..2 * sin t, r ^ 4 * cos t * sin t ^ 2 := by
    refine integral_normal_domain_cc' (g := fun t => 2 * sin t) continuousOn_sin (by fun_prop)
      pi_div_two_pos.le ?_ (by fun_prop)
    intro t ⟨h1, h2⟩; rw [two_mul, le_add_iff_nonneg_right]
    apply sin_nonneg_of_nonneg_of_le_pi h1; linarith
  _ = 31 / 5 * ∫ (x : ℝ) in 0..π / 2, sin x ^ 7 * cos x ^ (2 * 0 + 1) := by simp; ring_nf; simp
  _ = 31 / 40 := by rw [integral_sin_pow_mul_cos_pow_odd]; norm_num

theorem Zad1d : ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ x + y}, p.1 - p.2 = 0 := by
  have : IsCompact {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ x + y} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply isClosed_le <;> fun_prop
    rw [Metric.isBounded_iff_subset_closedBall (0, 0)]; use 2
    simp [Set.subset_def, Prod.dist_eq, abs_le]; intro a b h
    have : (a - 2⁻¹) ^ 2 + (b - 2⁻¹) ^ 2 ≤ 2⁻¹ := by nlinarith
    and_intros <;> nlinarith
  rw [MeasureTheory.integral_sub (continuousOn_fst.integrableOn_compact this)
      (continuousOn_snd.integrableOn_compact this), sub_eq_zero,
    ← MeasureTheory.integral_indicator (by simp; fun_prop), Measure.volume_eq_prod,
    ← integral_prod_swap, ← MeasureTheory.integral_indicator (by simp; fun_prop)]
  simp [Set.indicator, add_comm]; rfl
