import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory intervalIntegral Real Topology Filter

theorem integral_region_retween_cc {F : α × ℝ → β} [MeasureSpace α] [SFinite (volume : Measure α)]
    [NormedAddCommGroup β] [NormedSpace ℝ β] (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) (hF : IntegrableOn F {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}) :
    ∫ p in {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}, F p = ∫ x in s, ∫ y in f x..g x, F (x, y) := calc
  ∫ p in {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}, F p
  _ = ∫ p, {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}.indicator F p := by
    symm; apply MeasureTheory.integral_indicator; exact measurableSet_region_between_cc hf hg hs
  _ = ∫ x, ∫ y, {(x, y) | (x ∈ s) ∧ y ∈ Set.Icc (f x) (g x)}.indicator F (x, y) := by
    rw [Measure.volume_eq_prod, integral_prod]
    rwa [integrable_indicator_iff (measurableSet_region_between_cc hf hg hs), ← Measure.volume_eq_prod]
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
    (hF : ContinuousOn F {(x, y) | (x ∈ Set.Icc a b) ∧ y ∈ Set.Icc (f x) (g x)}) :
    ∫ p in {(x, y) | (x ∈ Set.Icc a b) ∧ y ∈ Set.Icc (f x) (g x)}, F p = ∫ x in a..b, ∫ y in f x..g x, F (x, y) := by
  rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hf' := (hf.measurable_piecewise continuous_zero.continuousOn measurableSet_Icc)
  have hg' := (hg.measurable_piecewise continuous_zero.continuousOn measurableSet_Icc)
  convert! integral_region_retween_cc hf' hg' measurableSet_Icc ?_ ?_ using 1
  · rw [setIntegral_congr_fun (measurableSet_region_between_cc hf' hg' (measurableSet_Icc (a := a) (b := b)))]
    · congr! 4; simp +contextual
    · apply Set.eqOn_refl
  · apply setIntegral_congr_fun measurableSet_Icc; intro x hx; simp [hx]
  · intro x hx; simp [hx, hfg]
  convert_to IntegrableOn F {(x, y) | (x ∈ Set.Icc a b) ∧ y ∈ Set.Icc (f x) (g x)}
  · ext p; simp +contextual
  apply hF.integrableOn_compact; apply Metric.isCompact_of_isClosed_isBounded
  · convert! (isClosed_Icc.epigraph hf).inter (isClosed_Icc.hypograph hg) using 1
    ext p; simp +contextual [and_assoc]
  obtain ⟨bf, hbf⟩ := isCompact_Icc.bddBelow_image hf; simp [lowerBounds, -Set.mem_Icc] at hbf
  obtain ⟨bg, hbg⟩ := isCompact_Icc.bddAbove_image hg; simp [upperBounds, -Set.mem_Icc] at hbg
  apply Bornology.IsBounded.subset (t := Set.Icc a b ×ˢ Set.Icc bf bg)
  · simp [Metric.isBounded_Icc]
  intro (x, y); simp [-Set.mem_Icc]; intro hx; simp [hx.1, hx.2]; grw [hbf x hx, ← hbg x hx]; trivial

theorem ContinuousLinearMap.det_dim2 [CommRing R] [TopologicalSpace R] (f : R × R →L[R] R × R) :
    f.det = (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2 := by
  simp [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd R),
    -LinearMap.det_toMatrix, Matrix.det_fin_two, LinearMap.toMatrix_apply]

namespace AM2.Cwi9

theorem Zad1a : ∫ p in {(x, y) | 0 ≤ x ∧ 0 ≤ y ∧ y ≤ 4 - x ^ 2 ∧ y ≤ 3 * √x}, p.1 * p.2 = 15 / 4 := calc
  ∫ p in {(x, y) | 0 ≤ x ∧ 0 ≤ y ∧ y ≤ 4 - x ^ 2 ∧ y ≤ 3 * √x}, p.1 * p.2
  _ = ∫ p in {(x, y) | (x ∈ Set.Icc 0 2) ∧ y ∈ Set.Icc 0 (min (4 - x ^ 2) (3 * √x))}, p.1 * p.2 := by
    congr! with p; simp; intros; suffices p.1 ^ 2 ≤ 4 by nlinarith
    grind
  _ = ∫ x in 0..2, ∫ y in 0..min (4 - x ^ 2) (3 * √x), x * y := by
    refine integral_normal_domain_cc (f := fun _ => 0) (g := fun x => min (4 - x ^ 2) (3 * √x))
      (by fun_prop) (by fun_prop) (by simp) ?_ (by fun_prop)
    intro x hx; simp at hx; positivity [show x ^ 2 ≤ 4 by nlinarith]
  _ = (∫ x in 0..1, ∫ y in 0..min (4 - x ^ 2) (3 * √x), x * y) +
      ∫ x in 1..2, ∫ y in 0..min (4 - x ^ 2) (3 * √x), x * y := by
    symm; apply integral_add_adjacent_intervals <;> apply Continuous.intervalIntegrable <;> fun_prop
  _ = (∫ x in 0..1, ∫ y in 0..3 * √x, x * y) + ∫ x in 1..2, ∫ y in 0..4 - x ^ 2, x * y := by
    congr 1; all_goals
      apply integral_congr; intro x hx; simp at hx; dsimp; congr; simp [-tsub_le_iff_right]; trans 3
    · simp [hx.2]
    · norm_num [le_sub_comm, abs_le, hx]; linarith
    · grw [← one_le_pow₀ hx.1]; norm_num
    · simp [hx.1]
  _ = (∫ x in 0..1, x * ∫ y in 0..3 * √x, y) + ∫ x in 1..2, x * ∫ y in 0..4 - x ^ 2, y := by
    congr! <;> apply intervalIntegral.integral_const_mul
  _ = (9 / 2) * (∫ x in 0..1, x * √x ^ 2) + ∫ x in 1..2, x * 8 - x ^ 3 * 4 + x ^ 5 / 2 := by
    norm_num [integral_id]; ring_nf; simp; ring
  _ = 3 / 2 + ∫ x in 1..2, x * 8 - x ^ 3 * 4 + x ^ 5 / 2 := by
    simp; rw [integral_congr (g := fun x => x ^ 2)] <;> norm_num +contextual [Set.EqOn, ← sq]
  _ = 15 / 4 := by
    rw [intervalIntegral.integral_add] <;> try apply Continuous.intervalIntegrable <;> fun_prop
    norm_num

/-
theorem Zad1b : ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y},
    1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) = idk := calc
  ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}, 1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ)
  _ = ∫ p, {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}.indicator
      (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) p := by
    rw [MeasureTheory.integral_indicator]; simp; fun_prop
  _ = ∫ p in polarCoord.target, p.1 * {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}.indicator
      (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) (polarCoord.symm p) := by
    rw [← integral_comp_polarCoord_symm]; simp
  _ = ∫ p in {(r, t) : ℝ × ℝ | r ∈ Set.Icc (1 / √2) 1 ∧ t ∈ Set.Icc 0 (arccos (r * √2)⁻¹)},
      p.1 * (fun (x, y) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) (polarCoord.symm p) := by
    generalize (fun ((x, y) : ℝ × ℝ) => 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ)) = f
    rw [← MeasureTheory.integral_indicator (by exact measurableSet_Ioi.prod measurableSet_Ioo),
        ← MeasureTheory.integral_indicator (by simp; fun_prop)]
    congr; ext x; simp [Set.indicator_apply, ← ite_and]; congr 1; simp [mul_pow, ← mul_add]; constructor
    · simp; intro hlr hlt hut hur h1 h2; sorry
    · simp; intro hlr hur hlt hut; sorry
  _ = ∫ p in {(r, t) : ℝ × ℝ | r ∈ Set.Icc (1 / √2) 1 ∧ t ∈ Set.Icc 0 (arccos (r * √2)⁻¹)},
      1 / p.1 ^ 2 := by
    simp [mul_pow, ← mul_add]; apply setIntegral_congr_fun (by simp; fun_prop); dsimp [Set.EqOn]
    intro x hx; rw [← rpow_natCast_mul]; norm_num; field; grw [← hx.1.1]; simp
  _ = ∫ r in 1 / √2..1, arccos (1 / (√2 * r)) / r ^ 2 := by
    rw [integral_normal_domain_cc (f := fun _ => 0) (g := fun r => arccos (r * √2)⁻¹)]
    · simp [mul_comm, inv_mul_eq_div]
    · fun_prop
    · sorry
    · simp; apply inv_le_one_of_one_le₀; simp
    · simp [arccos_nonneg]
    · fun_prop (disch := simp_all; intro a _ h _ _ _; apply ne_of_gt; grw [← h]; simp)
  _ = idk := sorry

theorem Zad1b' : ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y},
    1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) = idk := by
  let f : ℝ × ℝ →L[ℝ] ℝ × ℝ := {
    toFun := fun (x, y) => (x / √2 - y / √2, x / √2 + y / √2)
    map_add' p q := by simp; ring_nf; trivial
    map_smul' c p := by simp; ring_nf; trivial
  }
  have : ∀ p, (f p).1 ^ 2 + (f p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    simp [f]; intro x y; ring_nf; simp; ring
  calc ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ x ≤ y ∧ 1 ≤ x + y}, 1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ)
  _ = ∫ p in f '' {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ 0 ≤ y ∧ 1 / √2 ≤ x},
      1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) := by
    congr! 2; ext p; simp; constructor
    · rintro ⟨h1, h2, h3⟩; use (p.1 / √2 + p.2 / √2), (p.2 / √2 - p.1 / √2); simp [f]
      ring_nf; simp; ring_nf; simp [h1, h2, ← add_mul, h3]
    · rintro ⟨a, b, ⟨h1, h2, h3⟩, rfl⟩; simp [this, h1]; simp [f]; ring_nf; simp [h2]; grw [← h3]; ring_nf; simp
  _ = ∫ p in {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 ≤ 1 ∧ 0 ≤ y ∧ 1 / √2 ≤ x},
      1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) := by
    rw [integral_image_eq_integral_abs_det_fderiv_smul (f' := fun _ => f)]
    · congr! 2; simp [this]; convert one_mul _; simp [ContinuousLinearMap.det_dim2, f]; ring_nf; simp
    · simp; fun_prop
    · intro x _; exact f.hasFDerivWithinAt
    · apply Function.Injective.injOn; intro p q h; simp [f] at h; ext
      · convert congr(($(h.1) + $(h.2)) / √2) <;> (ring_nf; simp)
      · convert congr(($(h.2) - $(h.1)) / √2) <;> (ring_nf; simp; ring)
  _ = ∫ p in {(x, y) : ℝ × ℝ | x ∈ Set.Icc (1 / √2) 1 ∧ y ∈ Set.Icc 0 √(1 - x ^ 2)},
      1 / (p.1 ^ 2 + p.2 ^ 2) ^ (3 / 2 : ℝ) := by
    congr! with p; rcases p with ⟨x, y⟩; constructor <;> simp +contextual
    · intro hr hy hx; and_intros
      · contrapose! hr; apply lt_of_lt_of_le (b := x ^ 2) <;> simp [lt_abs, hr, sq_nonneg]
      · exact le_sqrt_of_sq_le (le_sub_iff_add_le'.mpr hr)
    · intro hlx hux hly huy; grw [huy]; rw [sq_sqrt]; simp
      grw [hux]; simp; grw [← hlx]; simp
  _ = ∫ x in 1 / √2..1, ∫ y in 0..√(1 - x ^ 2), 1 / (x ^ 2 + y ^ 2) ^ (3 / 2 : ℝ) := by
    apply integral_normal_domain_cc (f := fun _ => 0) (g := fun x => √(1 - x ^ 2)) (by fun_prop)
      (by fun_prop) (by simp; apply inv_le_one_of_one_le₀; simp) (by simp)
    apply continuousOn_const.div₀ (Continuous.continuousOn (by fun_prop (disch := norm_num)))
    simp; intro x y hlx hux hly huy; apply ne_of_gt; apply rpow_pos_of_pos
    grw [← hlx, ← sq_nonneg y]; simp
  _ = idk := sorry
-/
