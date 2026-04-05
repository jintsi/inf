import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.BoxIntegral.Integrability

/-! # Specialize BoxIntegral theorems to ℝ -/

open BoxIntegral MeasureTheory Topology Filter

variable {a b : ℝ} (hab : a < b) {n : ℕ} (hn : n ≠ 0)

/-- An interval `Set.Ioc a b`, as a `BoxIntegral.Box`. -/
abbrev BoxIntegral.interval (a b : ℝ) (hab : a < b) : Box Unit where
  lower _ := a
  upper _ := b
  lower_lt_upper _ := hab

theorem BoxIntegral.mem_interval (i : Unit → ℝ) : i ∈ interval a b hab ↔ i () ∈ Set.Ioc a b :=
  Unique.forall_iff

/-- An `i`th subinterval of `intervalPartition hab n`. -/
noncomputable def BoxIntegral.intervalBox (i : ℕ) : Box Unit :=
  interval (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n) (by gcongr <;> simp [hab])

open Classical in
/-- A partition of `Set.Ioc a b` into `n` intervals of length `(b - a) / n`. -/
noncomputable def BoxIntegral.intervalPartition : Prepartition (interval a b hab) where
  boxes := (Finset.range n).image (intervalBox hab hn)
  le_of_mem' := by
    simp [intervalBox, fun I J => (Box.le_TFAE I J).out 0 3, Pi.le_def]; intro i hi; as_aux_lemma =>
      use (by bound); have : (i + 1 : ℝ) ≤ n := by norm_cast
      field_simp; rw [← le_sub_iff_add_le', ← sub_mul]; gcongr; bound
  pairwiseDisjoint := by
    rw [Finset.coe_image, Finset.coe_range]; apply Set.Pairwise.image; unfold Set.Pairwise Function.onFun
    simp_rw [Set.mem_Iio]; intro i hi j hj hne; apply Disjoint.of_image (f := Equiv.funUnique _ _)
    simp_rw [Equiv.image_eq_preimage_symm, Equiv.funUnique_symm_apply, Set.preimage, intervalBox,
      Box.mem_coe, mem_interval, uniqueElim_const, Set.setOf_mem_eq, Set.Ioc_disjoint_Ioc]
    have := sub_pos_of_lt hab
    rw [← add_min, ← add_max, min_div_div_right, max_div_div_right,
      ← mul_min_of_nonneg, ← mul_max_of_nonneg, ← Nat.cast_add_one, ← Nat.cast_add_one,
      ← Nat.cast_min, ← Nat.cast_max, ← min_add] <;> try positivity
    gcongr; exact min_lt_max.mpr hne

/-- The index of the subinterval `x` is located in. -/
noncomputable def BoxIntegral.intervalPartition_index (a b : ℝ) (n : ℕ) (x : Unit → ℝ) :=
  ⌈(x () - a) * n / (b - a)⌉₊ - 1

theorem BoxIntegral.mem_intervalBox_index (x : Unit → ℝ) (hx : a < x ()) :
    x ∈ intervalBox hab hn (intervalPartition_index a b n x) := by
  rw [intervalBox, intervalPartition_index, Box.mem_mk, Unique.forall_iff, Set.mem_Ioc]; and_intros
  · rw [← lt_sub_iff_add_lt', div_lt_iff₀ (by simp; lia), ← lt_div_iff₀' (by simpa),
      Nat.cast_pred (by simp; bound [Nat.zero_lt_of_ne_zero hn]), sub_lt_iff_lt_add]
    apply Nat.ceil_lt_add_one; bound
  · rw [← sub_le_iff_le_add', le_div_iff₀ (by simp; lia), ← div_le_iff₀' (by simpa),
      Nat.cast_pred (by simp; bound [Nat.zero_lt_of_ne_zero hn]), sub_add_cancel]
    exact Nat.le_ceil _

theorem BoxIntegral.index_intervalBox (i : ℕ) :
    intervalPartition_index a b n (intervalBox hab hn i).upper = i := by
  simp_rw [intervalPartition_index, intervalBox, add_sub_cancel_left]
  rw [div_mul_cancel₀ _ (by positivity), mul_div_cancel_left₀ _ (sub_ne_zero.mpr hab.ne'),
    ← Nat.cast_add_one, Nat.ceil_natCast, Nat.add_one_sub_one]

include hab hn in
lemma BoxIntegral.intervalPartition_index_lt (x : Unit → ℝ) (hx : a < x () ∧ x () ≤ b) :
    intervalPartition_index a b n x < n := by
  rw [intervalPartition_index]
  apply Nat.sub_one_lt_of_le (by simp; bound [Nat.zero_lt_of_ne_zero hn, hx])
  rw [Nat.ceil_le, mul_div_right_comm, mul_le_iff_le_one_left (by simp; lia), div_le_one₀ (by simpa)]
  simpa using hx.2

theorem BoxIntegral.intervalPartition_isPartition : (intervalPartition hab hn).IsPartition := by
  simp_rw [Prepartition.IsPartition, Box.mem_mk, Set.mem_Ioc, intervalPartition,
    Prepartition.mem_mk, Finset.exists_mem_image, Finset.mem_range]
  refine fun x hx => ⟨intervalPartition_index a b n x, ?_, mem_intervalBox_index hab hn x (hx _).1⟩
  exact intervalPartition_index_lt hab hn x (hx _)

/-- `intervalPartition` with subintervals tagged by `t`. -/
noncomputable def BoxIntegral.taggedIntervalPartition' (t : ℕ → ℝ)
    (ht : ∀ i < n, t i ∈ Set.Icc a b) : TaggedPrepartition (interval a b hab) where
  toPrepartition := intervalPartition hab hn
  tag := fun J _ => if J.upper () ≤ a ∨ b < J.upper () then b else t (intervalPartition_index a b n J.upper)
  tag_mem_Icc := by
    intro ⟨l, u, hlt⟩; dsimp only; split
    case isTrue => exact Box.upper_mem_Icc _
    case isFalse h =>
      simp? at h says simp only [not_or, not_le, not_lt] at h
      rw [Box.Icc_eq_pi, Set.mem_univ_pi, Unique.forall_iff]
      apply ht; apply intervalPartition_index_lt hab hn u h

/-- `taggedIntervalPartition'` with stronger prerequisites to make it Henstock. -/
noncomputable abbrev BoxIntegral.taggedIntervalPartition (t : ℕ → ℝ)
    (ht : ∀ i : ℕ, t i ∈ Set.Icc (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n)) :
    TaggedPrepartition (interval a b hab) :=
  taggedIntervalPartition' hab hn t fun i hi => Set.mem_of_mem_of_subset (ht i) (by
      rw [Set.Icc_subset_Icc_iff (by bound), le_add_iff_nonneg_right]
      exact intervalPartition._proof_7 hab hn i hi)

theorem BoxIntegral.intervalPartition_isHenstock (t : ℕ → ℝ)
    (ht : ∀ i : ℕ, t i ∈ Set.Icc (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n)) :
    (taggedIntervalPartition hab hn t ht).IsHenstock := by
  simp_rw [TaggedPrepartition.IsHenstock, taggedIntervalPartition', TaggedPrepartition.mem_mk,
    intervalPartition, Prepartition.mem_mk, Finset.forall_mem_image, Finset.mem_range,
    Box.Icc_eq_pi, Set.mem_univ_pi, Unique.forall_iff, intervalBox]
  intro i hi; rw [ite_cond_eq_false, intervalPartition_index, add_sub_cancel_left,
    div_mul_cancel₀ _ (by simpa), mul_div_cancel_left₀ _ (by bound), ← Nat.cast_add_one,
    Nat.ceil_natCast, Nat.add_one_sub_one]; exact_mod_cast ht i
  · rw [add_le_iff_nonpos_right, eq_iff_iff, iff_false, not_or, not_lt, not_le]; and_intros
    · bound
    · exact (intervalPartition._proof_7 hab hn i hi).right

open Classical in
theorem BoxIntegral.intervalPartition_isSubordinate (t : ℕ → ℝ)
    (ht : ∀ i : ℕ, t i ∈ Set.Icc (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n))
    (r : ℝ) (hr₀ : 0 < r) (hr : (b - a) / n ≤ r) :
    (taggedIntervalPartition hab hn t ht).IsSubordinate fun _ => ⟨r, hr₀⟩ := by
  intro J hJ x hx; simp only
  grw [Metric.mem_closedBall, Metric.dist_le_diam_of_mem J.isBounded_Icc hx
    (intervalPartition_isHenstock hab hn t ht J hJ)]
  apply Metric.diam_le_of_forall_dist_le hr₀.le
  simp_rw [dist_pi_le_iff hr₀.le, Box.Icc_eq_pi, Set.mem_univ_pi, Unique.forall_iff]
  intro x hx y hy; grw [Metric.dist_le_diam_of_mem (Metric.isBounded_Icc _ _) hx hy,
    Real.diam_Icc (J.lower_le_upper ())]
  simp_rw [taggedIntervalPartition', intervalPartition, TaggedPrepartition.mem_mk,
    Prepartition.mem_mk, Finset.mem_image, intervalBox] at hJ
  obtain ⟨_, _, hJ⟩ := hJ; rw [← hJ]
  simp_rw [add_sub_add_left_eq_sub, mul_add_one, add_div, add_sub_cancel_left]; assumption

theorem BoxIntegral.tendsto_intervalPartition_toFilteriUnion (t : ℕ → ℕ → ℝ)
    (ht : ∀ n : ℕ, n ≠ 0 → ∀ i : ℕ, t n i ∈ Set.Icc (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n)) :
    Tendsto (fun n : ℕ => taggedIntervalPartition hab n.succ_ne_zero (t (n + 1)) (ht _ n.succ_ne_zero))
    atTop (IntegrationParams.Riemann.toFilteriUnion (interval a b hab) ⊤) := by
  simp_rw [(IntegrationParams.Riemann.hasBasis_toFilteriUnion_top _).tendsto_right_iff,
    IntegrationParams.RCond, IntegrationParams.Riemann, true_implies]; intro r hr
  simp_rw [exists_and_right, Set.mem_setOf, eventually_and]; and_intros; swap
  · simp [TaggedPrepartition.IsPartition, taggedIntervalPartition', intervalPartition_isPartition]
  rw [eventually_atTop]; use ⌈(b - a) / r 0 0⌉₊; intro n hn; use 0; constructor <;>
    try simp only [true_implies, Bool.false_eq_true, false_implies, intervalPartition_isHenstock]
  convert intervalPartition_isSubordinate hab n.succ_ne_zero (t n.succ) (ht n.succ n.succ_ne_zero)
    (r 0 0) (r 0 0).property ?_ using 2
  · apply hr
  · rw [ge_iff_le, Nat.ceil_le, div_le_iff₀ (r 0 0).property] at hn; field_simp; simp; grind


variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A function `f : ℝ → E` continuous on `Set.Icc a b` is box integrable. -/
theorem ContinuousOn.hasBoxIntegral_dim1 {f : ℝ → E} (hc : ContinuousOn f (Set.Icc a b))
    (l : IntegrationParams := IntegrationParams.Riemann) :
    HasIntegral (interval a b hab) l (fun x => f (x ())) BoxAdditiveMap.volume
    (∫ x in a..b, f x) := by
  convert ContinuousOn.hasBoxIntegral (E := E) (volume : Measure (Unit → ℝ)) ?_ l
  · simp [Box.toSet, Unique.forall_iff, intervalIntegral.integral_of_le hab.le]
    convert setIntegral_map_equiv (MeasurableEquiv.funUnique Unit ℝ) f _
    exact (volume_preserving_funUnique Unit ℝ).map_eq.symm
  · apply hc.comp (continuousOn_apply () _)
    simp [Set.MapsTo, Box.Icc]; tauto

theorem ContinuousOn.tendsto_integralSum_intervalIntegral {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc a b)) (l : IntegrationParams := IntegrationParams.Riemann) :
    Tendsto (fun π => ∑ J ∈ π.boxes, (J.upper () - J.lower ()) • f (π.tag J ()))
    (l.toFilteriUnion (interval a b hab) ⊤) (𝓝 (∫ x in a..b, f x)) := by
  convert (config := {transparency := .default}) hc.hasBoxIntegral_dim1 hab l with _ J _
  rw [Measure.toBoxAdditive_apply, Measure.real_def, Box.coe_eq_pi,
    Real.volume_pi_Ioc_toReal J.lower_le_upper, Fintype.prod_unique]

open Classical in
include hab in
theorem tendsto_sum_intervalIntegral {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc a b)) {t : ℕ → ℕ → ℝ}
    (ht : ∀ n : ℕ, n ≠ 0 → ∀ i : ℕ, t n i ∈ Set.Icc (a + (b - a) * i / n) (a + (b - a) * (i + 1) / n)) :
    Tendsto (fun n : ℕ => ((b - a) / n) • ∑ i ∈ Finset.range n, f (t n i)) atTop (𝓝 (∫ x in a..b, f x)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  convert (hc.tendsto_integralSum_intervalIntegral hab).comp
    (tendsto_intervalPartition_toFilteriUnion hab t ht) with n
  dsimp; simp_rw [taggedIntervalPartition', intervalPartition]
  rw [Finset.sum_image, Finset.smul_sum]; congr! 2 with i hi
  · simp_rw [intervalBox]; ring
  · rw [ite_cond_eq_false, index_intervalBox]
    simp_rw [intervalBox]
    rw [add_le_iff_nonpos_right, eq_iff_iff, iff_false, not_or, not_lt, not_le]; and_intros
    · bound
    · exact (intervalPartition._proof_7 hab n.succ_ne_zero i (by simpa using hi)).right
  · intro i hi j hj h
    apply_fun fun J => intervalPartition_index a b (n + 1) J.upper at h
    rw [index_intervalBox, index_intervalBox] at h; exact h

include hab in
theorem tendsto_sum_left_intervalIntegral {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc a b)) : Tendsto (fun n : ℕ => ((b - a) / n) •
    ∑ i ∈ Finset.range n, f (a + (b - a) * i / n)) atTop (𝓝 (∫ x in a..b, f x)) :=
  tendsto_sum_intervalIntegral hab hc fun n hn i =>
    Set.left_mem_Icc.mpr (by field_simp; grind)

include hab in
theorem tendsto_sum_right_intervalIntegral {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc a b)) : Tendsto (fun n : ℕ => ((b - a) / n) •
    ∑ i ∈ Finset.range n, f (a + (b - a) * (i + 1) / n)) atTop (𝓝 (∫ x in a..b, f x)) :=
  tendsto_sum_intervalIntegral hab hc fun n hn i =>
    Set.right_mem_Icc.mpr (by field_simp; grind)

include hab in
theorem tendsto_sum_midpoint_intervalIntegral {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc a b)) : Tendsto (fun n : ℕ => ((b - a) / n) •
    ∑ i ∈ Finset.range n, f (a + (b - a) * (i + 2⁻¹) / n)) atTop (𝓝 (∫ x in a..b, f x)) :=
  tendsto_sum_intervalIntegral hab hc fun n hn i =>
    Set.mem_Icc.mpr (by field_simp; grind)

theorem tendsto_sum_left_intervalIntegral_zero {a : ℝ} (ha : 0 < a)
    {f : ℝ → E} (hc : ContinuousOn f (Set.Icc 0 a)) : Tendsto (fun n : ℕ => (a / n) •
    ∑ i ∈ Finset.range n, f (a * i / n)) atTop (𝓝 (∫ x in 0..a, f x)) := by
  convert tendsto_sum_left_intervalIntegral ha hc using 5 <;> simp

theorem tendsto_sum_right_intervalIntegral_zero {a : ℝ} (ha : 0 < a)
    {f : ℝ → E} (hc : ContinuousOn f (Set.Icc 0 a)) : Tendsto (fun n : ℕ => (a / n) •
    ∑ i ∈ Finset.range n, f (a * (i + 1) / n)) atTop (𝓝 (∫ x in 0..a, f x)) := by
  convert tendsto_sum_right_intervalIntegral ha hc using 5 <;> simp

theorem tendsto_sum_right_intervalIntegral_zero_one {f : ℝ → E}
    (hc : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f ((i + 1) / n)) atTop (𝓝 (∫ x in 0..1, f x)) := by
  convert tendsto_sum_right_intervalIntegral zero_lt_one hc using 3 <;> simp
