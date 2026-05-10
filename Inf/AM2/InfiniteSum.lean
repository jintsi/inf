import Inf.AM1.Tendsto
import Mathlib.Tactic.Peel

/-! ## Worth noting:

"Regular" series convergence, i.e. as a sequence of parital sums, is implemented im Mathlib
as `Summable f (conditional ℕ)`, while unqualified `Summable f` denotes absolute convergence.

The API for working with `conditional ℕ` is surprisingly underdeveloped. That's where this file comes in. -/

open Topology Filter SummationFilter Finset

/-- A series `∑'[conditional ℕ] n, f n` (starting at 0!) converges (along `conditional ℕ`) iff
the sequence of partial sums `∑ i ∈ range n, f i` converges. -/
theorem summable_conditional_iff [AddCommMonoid α] [TopologicalSpace α] {f : ℕ → α} :
    Summable f (conditional ℕ) ↔ ∃ a, Tendsto (fun n => ∑ i ∈ range n, f i) atTop (𝓝 a) := by
  simp only [Summable, HasSum, conditional_filter_eq_map_range, tendsto_map'_iff]; rfl

/-- For the unconditional version, see `summable_congr_atTop`. -/
theorem summable_congr_atTop' [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α]
    {f g : ℕ → α} (h : f =ᶠ[Filter.atTop] g) : Summable f (conditional ℕ) ↔ Summable g (conditional ℕ) := by
  simp only [EventuallyEq, eventually_atTop, ge_iff_le] at h; obtain ⟨n₀, hn₀⟩ := h
  exact summable_iff_of_summable_sub (summable_of_ne_finset_zero (s := range n₀) (by simpa [sub_eq_zero]))

alias ⟨Summable.congr_atTop', _⟩ := summable_congr_atTop'

/-- An absolutely convergent series also converges conditionally. -/
theorem Summable.to_conditional [AddCommMonoid α] [TopologicalSpace α] {f : ℕ → α} (h : Summable f) :
    Summable f (conditional ℕ) := h.mono_filter (conditional ℕ).le_atTop

/-- A series converges unconditionally iff it converges absolutely. -/
theorem summable_iff_summable_abs_conditional {f : ℕ → ℝ} :
    Summable f ↔ Summable (fun n => |f n|) (conditional ℕ) := by
  use fun h => h.abs.to_conditional
  rw [summable_conditional_iff]; exact summable_of_absolute_convergence_real

theorem summable_iff_conditional_of_nonneg_atTop {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, 0 ≤ f n) :
    Summable f ↔ Summable f (conditional ℕ) := by
  rw [summable_iff_summable_abs_conditional]; apply summable_congr_atTop'
  filter_upwards [hf] with a using abs_of_nonneg

theorem summable_iff_conditional_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ Summable f (conditional ℕ) :=
  summable_iff_conditional_of_nonneg_atTop (Eventually.of_forall hf)

/-- For the unconditional version, see `Summable.tendsto_atTop_zero`. -/
theorem Summable.tendsto_atTop_zero' [AddCommGroup α] [TopologicalSpace α] [ContinuousSub α]
    {f : ℕ → α} (hf : Summable f (conditional ℕ)) : Tendsto f atTop (𝓝 0) := by
  have ⟨a, ha⟩ := summable_conditional_iff.mp hf
  simpa [sum_range_succ] using (ha.comp (tendsto_add_atTop_nat 1)).sub ha

theorem Summable.shift [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α] {f : β → α}
    [CompleteSpace α] [Add β] [IsRightCancelAdd β] (hf : Summable f) (a : β) :
    Summable (fun x => f (x + a)) := hf.comp_injective (add_left_injective a)

/-! ## Comparison test

Unconditional version is `Summable.of_nonneg_of_le`. -/

theorem Summable.of_nonneg_atTop_of_le_atTop {f g : ℕ → ℝ} (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (hgf : ∀ᶠ n in atTop, g n ≤ f n) (hf : Summable f) : Summable g := by
  let G := fun n => max 0 (g n); let F := fun n => max (f n) (G n)
  have : Summable F := hf.congr_atTop (by filter_upwards [hg, hgf]; simp +contextual [F, G])
  have : Summable G := this.of_nonneg_of_le (by simp [G]) (by simp [F])
  exact this.congr_atTop (by filter_upwards [hg]; simp [G])

/-! ## Ratio test -/

theorem not_summable_of_eventually_gt_one' [SeminormedAddCommGroup α] {f : ℕ → α}
    (h : ∀ᶠ n in atTop, 1 < ‖f (n + 1)‖ / ‖f n‖) : ¬Summable f (conditional ℕ) := by
  rcases by simpa [one_lt_div_iff, not_lt_of_ge] using h with ⟨a, ha⟩
  apply mt Summable.tendsto_atTop_zero'; rw [tendsto_zero_iff_norm_tendsto_zero]
  apply mt (Tendsto.eventually_lt_const (ha a le_rfl).1)
  rw [not_eventually]; apply Eventually.frequently; simp only [not_lt, eventually_atTop, ge_iff_le]
  use a; peel ha with b hb ha'; clear ha'; induction b, hb using Nat.le_induction
  case base => rfl
  case succ n hn ih => exact ih.trans (ha n hn).2.le

theorem not_summable_of_ratio_test_tendsto_gt_one'[SeminormedAddCommGroup α] {f : ℕ → α} {l : ℝ}
    (hl : 1 < l) (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f (conditional ℕ) := not_summable_of_eventually_gt_one' (h.eventually_const_lt hl)

/-! ## Root test -/

theorem summable_pow_of_tendsto {f : ℕ → ℝ} (hl : |l| < 1) (hf : Tendsto f atTop (𝓝 l)) :
    Summable (fun n => f n ^ n) := by
  apply Summable.of_abs; simp_rw [abs_pow]
  obtain ⟨r, hlr, hr1⟩ := exists_between hl
  apply Summable.of_nonneg_atTop_of_le_atTop (f := fun n => r ^ n) (by simp)
  · filter_upwards [hf.abs.eventually_le_const hlr] with n hf using pow_le_pow_left₀ (abs_nonneg _) hf n
  · exact summable_geometric_of_lt_one (by grw [← hlr, abs_nonneg]) hr1

theorem summable_of_tendsto_rpow_inv [SeminormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α}
    (hl : l < 1) (h : Tendsto (fun n => ‖f n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 l)) : Summable f := by
  have : 0 ≤ l := ge_of_tendsto' h (by bound)
  apply Summable.of_norm
  apply (summable_pow_of_tendsto (show |l| < 1 by simp [abs_lt]; bound) h).congr_atTop
  filter_upwards [eventually_ne_atTop 0] with a using Real.rpow_inv_natCast_pow (norm_nonneg _)

theorem not_summable_of_tendsto_rpow_inv [SeminormedAddCommGroup α] {f : ℕ → α} (hl : 1 < l)
    (h : Tendsto (fun n => ‖f n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 l)) : ¬Summable f (conditional ℕ) := by
  apply mt Summable.tendsto_atTop_zero'; rw [tendsto_zero_iff_norm_tendsto_zero]
  suffices ∀ᶠ n in atTop, 1 ≤ ‖f n‖ from mt (fun h => ge_of_tendsto h this) (by simp)
  filter_upwards [h.eventually_const_lt hl]; simp [Real.one_lt_rpow_iff]; bound

/-! ## Alternating series test -/

theorem summable_alternating_of_antitone_tendsto_zero {f : ℕ → ℝ} (hf : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : Summable (fun n => (-1) ^ n * f n) (conditional ℕ) :=
  summable_conditional_iff.mpr (hf.tendsto_alternating_series_of_tendsto_zero hf0)

theorem summable_alternating_of_antitone_tendsto_zero' {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, f (n + 1) ≤ f n)
    (hf0 : Tendsto f atTop (𝓝 0)) : Summable (fun n => (-1) ^ n * f n) (conditional ℕ) := by
  rcases by simpa using hf with ⟨a, ha⟩; let F n := if n < a then f a else f n
  have : Antitone F := antitone_nat_of_succ_le (by grind)
  apply (summable_alternating_of_antitone_tendsto_zero this (hf0.congr'
      (by simp [EventuallyEq, F]; use a; simp +contextual))).congr_atTop'
  simp [EventuallyEq, F]; use a; simp +contextual

/-! ## Power series -/

/-- An inverse ratio test for power series. -/
theorem summable_powerSeries_of_norm_lt_of_tendsto [NormedRing α] [NormMulClass α]
    [CompleteSpace α] {f : ℕ → α} (hf : Tendsto (fun n => ‖f n‖ / ‖f (n + 1)‖) atTop (𝓝 r))
    {x : α} (hx : ‖x‖ < r) : Summable fun n => f n * x ^ n := by
  have hr : 0 < r := hx.trans_le' (norm_nonneg x)
  by_cases! h : x = 0
  · subst h; exact summable_of_ne_finset_zero (s := {0}) (by simp +contextual)
  apply summable_of_ratio_test_tendsto_lt_one (l := ‖x‖ / r)
  · rwa [div_lt_one hr]
  · filter_upwards [hf.eventually_ne hr.ne'] with n hn; simp_all [pow_ne_zero]
  convert hf.const_div ‖x‖ hr.ne' using 2 with n; simp [pow_succ]; field

theorem not_summable_powerSeries_of_norm_gt_of_tendsto [NormedRing α] [NormMulClass α] {f : ℕ → α}
    (hf : Tendsto (fun n => ‖f n‖ / ‖f (n + 1)‖) atTop (𝓝 r)) (hf' : ∀ᶠ n in atTop, f n ≠ 0)
    {x : α} (hx : r < ‖x‖) : ¬Summable (fun n => f n * x ^ n) (conditional ℕ) := by
  apply not_summable_of_eventually_gt_one'
  filter_upwards [hf.eventually_lt_const hx, hf', (tendsto_add_atTop_nat 1).eventually hf']
  have := ne_zero_of_norm_ne_zero (hx.trans_le' (ge_of_tendsto' hf fun n => by bound)).ne'
  intros; simp [pow_succ]; field_simp at *; assumption

theorem summable_powerSeries_of_norm_lt_inv [SeminormedRing α] [NormOneClass α] [NormMulClass α]
    [CompleteSpace α] {f : ℕ → α} (hf : Tendsto (fun n => ‖f n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 r))
    {x : α} (hx : ‖x‖ < r⁻¹) : Summable fun n => f n * x ^ n := by
  apply summable_of_tendsto_rpow_inv (l := r * ‖x‖)
  · have : 0 < r := by rw [← inv_pos]; exact hx.trans_le' (norm_nonneg x)
    simpa [← lt_inv_mul_iff₀ this]
  apply (hf.mul_const ‖x‖).congr'; filter_upwards [eventually_ne_atTop 0]
  simp +contextual [Real.mul_rpow, Real.pow_rpow_inv_natCast]

theorem not_summable_powerSeries_of_norm_gt_inv [SeminormedRing α] [NormOneClass α] [NormMulClass α]
    {f : ℕ → α} (hf : Tendsto (fun n => ‖f n‖ ^ (n : ℝ)⁻¹) atTop (𝓝 r)) (hr : r ≠ 0)
    {x : α} (hx : r⁻¹ < ‖x‖) : ¬Summable (fun n => f n * x ^ n) (conditional ℕ) := by
  apply not_summable_of_tendsto_rpow_inv (l := r * ‖x‖)
  · rwa [← inv_lt_iff_one_lt_mul₀' ((ge_of_tendsto' hf (by bound)).lt_of_ne' hr)]
  apply (hf.mul_const ‖x‖).congr'; filter_upwards [eventually_ne_atTop 0]
  simp +contextual [Real.mul_rpow, Real.pow_rpow_inv_natCast]
