import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

open Topology Filter

namespace AM2.Cwi6

/-- Specialization of `isClosed_singleton` to metric spaces. -/
theorem Zad4 [MetricSpace X] {x : X} : IsClosed {x} := isClosed_singleton

alias Zad5a := IsOpen.inter
alias Zad5b := isOpen_iUnion
/-- This fails to hold when `ι` is infinite.

**Alias** of `isOpen_iInter_of_finite`. -/
alias Zad5c := isOpen_iInter_of_finite

/-- Not that here we have to explicitly specify that x ≠ 0. -/
abbrev Zad6.A := {(x, y) : ℝ × ℝ | x ≠ 0 ∧ (x ^ 2 - y - 1) / x ≤ 0}

open Zad6 in
theorem Zad6a : ¬IsOpen A := by
  simpa [Metric.isOpen_iff, Metric.ball, dist] using
    ⟨1, one_ne_zero, 0, by simp, fun e he => ⟨1, by simpa, -e / 2, by grind, by simpa [neg_div]⟩⟩

open Zad6 in
theorem Zad6b : ¬IsClosed A := by
  simpa [← isOpen_compl_iff, Metric.isOpen_iff, Metric.ball, Set.subset_def, dist] using
    ⟨0, -1, by tauto, fun e he => ⟨-e / 2, by grind, -1, by simpa, by linarith, by simp [sq]; linarith⟩⟩

open ContractingWith in
theorem Zad7 {n : ℕ} (hn : n ≠ 0) : ∃! x ∈ Set.Ioo (0 : ℝ) 1, x ^ n - (n + 1) * (1 - x) = 0 := by
  let f' := fun (x : ℝ) => 1 - x ^ n / (n + 1)
  suffices ∃! x ∈ Set.Ioo 0 1, f' x = x by grind
  have hf' : Set.MapsTo f' (Set.Icc 0 1) (Set.Icc 0 1) := by
    simp [Set.MapsTo, f']; intro x h0 h1; have := pow_le_one₀ (n := n) h0 h1; bound
  let f := hf'.restrict
  suffices ∃ x : Set.Icc 0 1, x ≠ 0 ∧ x ≠ 1 ∧ f.IsFixedPt x ∧ ∀ y, f.IsFixedPt y → y = x by
    obtain ⟨⟨x, hx⟩, h0, h1, hf, hu⟩ := this
    have hx := (Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hx).resolve_left (by contrapose h0; congr)
      |>.resolve_left (by contrapose h1; congr)
    use x, ⟨hx, Subtype.ext_iff.mp hf⟩, fun y ⟨hy, hf⟩ => Subtype.ext_iff.mp <|
      hu ⟨y, Set.mem_Icc_of_Ioo hy⟩ (Subtype.ext hf)
  use fixedPoint (K := n / (n + 1)) f ?_, ?_, ?_, fixedPoint_isFixedPt ?_, fun y => fixedPoint_unique ?_
  · simp [ContractingWith, lipschitzWith_iff_dist_le_mul, -NNReal.coe_div, f, Subtype.dist_eq,
      -Set.mem_Icc, ← lipschitzOnWith_iff_dist_le_mul]; use by bound
    apply (convex_Icc 0 1).lipschitzOnWith_of_nnnorm_deriv_le (by fun_prop)
    intro x hx; simp [f', ← Nat.cast_add_one, -Nat.cast_add]; field_simp
    apply pow_le_one₀ (by simp); rw [x.nnnorm_of_nonneg hx.left, ← NNReal.coe_le_one]; exact hx.right
  all_goals
    intro h; have := h ▸ fixedPoint_isFixedPt _
    simp [Function.IsFixedPt, f, Subtype.ext_iff, f', hn, n.cast_add_one_ne_zero] at this
