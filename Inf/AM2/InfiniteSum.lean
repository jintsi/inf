import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

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
  apply summable_iff_of_summable_sub; rw [summable_conditional_iff]
  exists ∑ x ∈ range n₀, (f x - g x); rw [← tendsto_add_atTop_iff_nat n₀]
  simp_rw [add_comm, sum_range_add]; convert tendsto_const_nhds using 2 with n
  rw [add_eq_left]; apply sum_eq_zero; intro i hi; rw [sub_eq_zero]; apply hn₀; simp

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

/-! # Comparison test

Unconditional version is `Summable.of_nonneg_of_le`. -/

theorem Summable.of_nonneg_atTop_of_le_atTop {f g : ℕ → ℝ} (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (hgf : ∀ᶠ n in atTop, g n ≤ f n) (hf : Summable f) : Summable g := by
  let G := fun n => max 0 (g n); let F := fun n => max (f n) (G n)
  have : Summable F := hf.congr_atTop (by filter_upwards [hg, hgf]; simp +contextual [F, G])
  have : Summable G := this.of_nonneg_of_le (by simp [G]) (by simp [F])
  exact this.congr_atTop (by filter_upwards [hg]; simp [G])

/- # Root test -/

theorem summable_pow_of_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 l)) (hl : |l| < 1) :
    Summable (fun n => f n ^ n) := by
  apply Summable.of_abs; simp_rw [abs_pow]
  obtain ⟨r, hlr, hr1⟩ := exists_between hl
  apply Summable.of_nonneg_atTop_of_le_atTop (f := fun n => r ^ n) (by simp)
  · filter_upwards [hf.abs.eventually_le_const hlr] with n hf using pow_le_pow_left₀ (abs_nonneg _) hf n
  · exact summable_geometric_of_lt_one (by grw [← hlr, abs_nonneg]) hr1
