import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Topology Filter

namespace AM1.Cwi3

/-- Here, it's significant that we're working with `PNat` and not `ℕ` -/
theorem Zad1a : Antitone fun (n : ℕ+) => (4 ^ n.val : ℚ) / (n.val + 2).factorial := by
  suffices Antitone fun n => (4 ^ (n + 1) : ℚ) / (n + 1 + 2).factorial by
    simp [Antitone] at *
    intro a b hab; specialize @this a.natPred b.natPred; simp at this; exact this hab
  apply antitone_nat_of_succ_le; intro n
  rw [div_le_div_iff₀, mul_comm (4 ^ (n + 1)), ←div_le_div_iff₀, Nat.factorial] <;> try positivity
  simp [Rat.pow_succ, mul_div_assoc]; rw [div_self] <;> try positivity
  linarith

theorem Zad1b_below : BddBelow (Set.range fun (n : ℕ) => 1 + (n : ℝ) ^ (3⁻¹ : ℝ)) := by
  simp [bddBelow_def]; exists 1; intro n; simp; positivity

theorem Zad1b_above : ¬BddAbove (Set.range fun (n : ℕ) => 1 + (n : ℝ) ^ (3⁻¹ : ℝ)) := by
  simp [bddAbove_def]; intro x; exists ⌈x⌉₊ ^ 3; simp
  rw [←Real.rpow_ofNat, Real.rpow_rpow_inv] <;> try simp
  grw [←Nat.le_ceil x]; simp

/-- The definition of convergence we're working with is `Metric.tendsto_atTop` with `Real.dist_eq` -/
theorem Zad2a : Tendsto (fun n => (2 * n - 1) / (4 * n + 1) : ℕ → ℝ) atTop (𝓝 (1 /2)) := by
  simp_rw [Metric.tendsto_atTop, Real.dist_eq]
  intro e he; exists ⌊(3 / (8 * e)) - (1 / 4)⌋₊ + 1; intro n hn
  field_simp; ring_nf; rw [abs_of_nonpos] <;> (simp; try positivity)
  replace hn := (Nat.lt_floor_add_one ((3 / (8 * e)) - (1 / 4))).trans_le
    (show _ ≤ (n : ℝ) by exact_mod_cast hn)
  rw [sub_lt_iff_lt_add, ← div_div, div_lt_comm₀] at hn <;> try positivity
  field_simp; field_simp at hn; linarith

theorem Zad2b : Tendsto (fun n => 3 - 2 * n : ℕ → ℝ) atTop atBot := by
  simp [tendsto_atTop_atBot]
  intro D; exists ⌊(3 - D) / 2⌋₊ + 1; intro n hn
  replace hn := lt_of_lt_of_le (Nat.lt_floor_add_one ((3 - D) / 2))
    (show _ ≤ (n : ℝ) by exact_mod_cast hn)
  linarith

theorem Zad3 : Tendsto (fun n => 3 ^ n / n.factorial : ℕ → ℝ) atTop (𝓝 0) :=
  FloorSemiring.tendsto_pow_div_factorial_atTop 3

theorem Zad4 {a : ℕ → ℝ} {g : ℝ} (hg : g ≠ 0) (h : Tendsto a atTop (𝓝 g)) :
    Tendsto (fun n => a n ^ (3⁻¹ : ℝ)) atTop (𝓝 (g ^ (3⁻¹ : ℝ))) := h.rpow_const (Or.inl hg)

theorem _root_.Filter.Tendsto.sqrt_atTop (h : Tendsto f l atTop) : Tendsto (fun x => √(f x)) l atTop :=
  Real.tendsto_sqrt_atTop.comp h

theorem Zad5a : Tendsto (fun n : ℕ => n ^ 2 / (√(n + 1) - √(n + 4))) atTop atBot := by
  apply Tendsto.congr (fun n => by
    rewrite [← mul_div_mul_left, ← sq_sub_sq, Real.sq_sqrt, Real.sq_sqrt]; norm_num; rfl
    all_goals positivity
  )
  have h1 := (tendsto_atTop_add_const_right _ 1 tendsto_id).sqrt_atTop
  have h2 := (tendsto_atTop_add_const_right _ 4 tendsto_id).sqrt_atTop
  exact (h1.atTop_add_atTop h2).atTop_mul_atTop₀ (tendsto_pow_atTop two_ne_zero)
    |>.atTop_div_const_of_neg (by simp) |>.comp tendsto_natCast_atTop_atTop

noncomputable def _root_.Real.cbrt := fun r : ℝ => r ^ (3⁻¹ : ℝ)

open Real

theorem Zad5b : Tendsto (fun n : ℕ => n * (cbrt (n ^ 3 + n) - n)) atTop (𝓝 (1 / 3)) := by
  apply Tendsto.congr'; symm; simp [EventuallyEq]; use 1; intro n hn; calc
    n * (cbrt (n ^ 3 + n) - n) = n * (n * (cbrt (1 + (↑n)⁻¹ ^ 2) - 1)) := by
      congr; rw [mul_sub, mul_one, cbrt, cbrt]; congr
      apply eq_mul_of_mul_inv_eq₀ (by positivity)
      rw [← Real.inv_rpow, ← Real.mul_rpow]; field_simp; simp; apply Real.pow_rpow_inv_natCast
      all_goals positivity
    _ = (cbrt (1 + (↑n)⁻¹ ^ 2) ^ 2 + cbrt (1 + (↑n)⁻¹ ^ 2) + 1)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left; ring_nf
      rw [cbrt, ← Nat.cast_ofNat (n := 3), Real.rpow_inv_natCast_pow]; field
      all_goals positivity
  have := by simpa using tendsto_natCast_atTop_atTop.inv_tendsto_atTop.pow 2
    |>.const_add 1 |>.rpow_const (p := 3⁻¹) (by simp)
  simp [cbrt, tendsto_inv_iff₀]; convert ((this.pow 2).add this).add_const 1; norm_num

theorem Zad5c : Tendsto (fun n : ℕ => (n ^ 2 + 5 : ℝ) ^ (n⁻¹ : ℝ)) atTop (𝓝 1) := by
  apply (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop).squeeze'
    ((tendsto_rpow_div_mul_add 2 1 (-1) zero_ne_one).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  · simp; use 0; intro n hn; apply Real.rpow_le_rpow <;> try positivity
    norm_cast; zify; grw [← Int.le_self_sq n]; simp
  · simp [div_eq_mul_inv]; use 2; intro n hn
    rw [Real.rpow_mul (by positivity)]; gcongr; norm_cast; linarith

theorem tendsto_const_rpow_inv (a : ℝ) (ha : 0 < a) : Tendsto (fun x : ℝ => a ^ x⁻¹) atTop (𝓝 1) := by
  wlog! ha' : 1 ≤ a
  · convert (this a⁻¹ (by simpa) (by bound)).inv₀ (by simp) using 2 <;> simp [Real.inv_rpow ha.le]
  apply tendsto_const_nhds.squeeze' tendsto_rpow_div
  · simpa using ⟨0, fun x hx => Real.one_le_rpow ha' (inv_nonneg.mpr hx)⟩
  · simpa using ⟨a, fun x hx => Real.rpow_le_rpow ha.le hx (by bound)⟩

theorem Zad5d : Tendsto (fun n : ℕ => (7 ^ n + (-3) ^ n : ℝ) ^ (n⁻¹ : ℝ)) atTop (𝓝 7) := by
  have := (isLittleO_pow_pow_of_abs_lt_left (show |-3| < |7| by norm_num)).right_isTheta_add'
  have ⟨c₁, hc₁, h₁⟩ := Asymptotics.isBigO_iff''.mp this.isBigO
  have ⟨c₂, hc₂, h₂⟩ := Asymptotics.isBigO_iff'.mp this.isBigO_symm
  simp [-eventually_atTop] at h₁ h₂
  suffices Tendsto (fun n : ℕ => |(7 ^ n + (-3) ^ n : ℝ)| ^ (n⁻¹ : ℝ)) atTop (𝓝 7) by
    apply this.congr; intro n; congr; simp
    rw [neg_pow]; cases neg_one_pow_eq_or ℝ n <;> simp [*]; positivity; bound
  apply Tendsto.squeeze' (g := fun n : ℕ => c₁ ^ (n⁻¹ : ℝ) * 7) (h := fun n : ℕ => c₂ ^ (n⁻¹ : ℝ) * 7)
  · simpa using ((tendsto_const_rpow_inv c₁ hc₁).comp tendsto_natCast_atTop_atTop).mul_const 7
  · simpa using ((tendsto_const_rpow_inv c₂ hc₂).comp tendsto_natCast_atTop_atTop).mul_const 7
  map_tacs [apply h₁.mp; apply h₂.mp]; all_goals
  · simp; use 1; intro n hn this
    convert Real.rpow_le_rpow (by bound) this (show 0 ≤ (n⁻¹ : ℝ) by simp) using 1
    rw [Real.mul_rpow, Real.pow_rpow_inv_natCast] <;> bound

theorem Zad6 {a : ℕ → ℤ} {g : ℤ} (h : Tendsto a atTop (𝓝 g)) : ∃ n₀, ∀ n ≥ n₀, a n = g := by
  simp_all

theorem Zad7_sup {a : ℕ → ℝ} (h : Tendsto a atTop (𝓝 0))
    (hp : ∀ n, 0 < a n) : iSup a ∈ Set.range a := by
  rw [Set.mem_range]
  have isup_pos := (lt_ciSup_iff h.bddAbove_range).mpr ⟨0, hp 0⟩
  have ⟨n₀, h₀⟩ : ∃ n₀, ∀ n ≥ n₀, a n ≤ iSup a / 2 := by
    simpa using h.eventually_le_const (half_pos isup_pos)
  have ⟨n', hn', h'⟩ : ∃ n' < n₀, ∀ n ≥ n₀, a n < a n' := by
    by_contra!; refine not_le_of_gt (half_lt_self isup_pos) (ciSup_le fun n' => ?_)
    by_cases! h : n' < n₀
    · exact (this n' h).elim fun n ⟨hn, h⟩ => h.trans (h₀ n hn)
    · exact h₀ n' h
  have ⟨n, hn, hs⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (ne_zero_of_lt hn')) a
  exists n
  refine ge_antisymm (ciSup_le ?bound) (le_ciSup h.bddAbove_range n)
  intro x; rw [← hs]; simp only [Finset.le_sup'_iff, Finset.mem_range]
  by_cases! hx : x < n₀
  · exists x
  · use n', hn', (h' x hx).le

theorem Zad7_inf {a : ℕ → ℝ} (h : Tendsto a atTop (𝓝 0))
    (hp : ∀ n, 0 < a n) : iInf a ∉ Set.range a := by
  suffices iInf a = 0 by simpa [this] using fun n => ne_of_gt (hp n)
  exact IsGLB.ciInf_eq (IsGLB.range_of_tendsto (fun n => (hp n).le) h)

theorem Zad13 : Antitone fun (n : ℕ+) => (1 + 1 / n : ℚ) ^ (n + 1 : ℕ) := by
  suffices Antitone fun n => (1 + 1 / (n + 1 : ℕ) : ℚ) ^ (n + 1 + 1) by
    intro a b hab; simpa using this (PNat.natPred_le_natPred.mpr hab)
  apply antitone_nat_of_succ_le; intro n
  rw [← one_le_div (by positivity), pow_succ _ (n + 1 + 1), ← div_div, ← div_pow,
      one_add_div (by positivity)]; nth_rw 1 [one_add_div (by positivity)]
  norm_cast; norm_num; rw [one_le_div (by positivity)]
  grw [show _ / _ = 1 + 1 / (↑n * 4 + ↑n ^ 2 + 3 : ℚ) by field,
    ← one_add_mul_le_pow (by trans 0; simp; positivity)]
  field_simp; grind

theorem Zad15 : ¬∀ a b : ℕ → ℝ, Tendsto (a * b) atTop (𝓝 0) →
    Tendsto a atTop (𝓝 0) ∨ Tendsto b atTop (𝓝 0) := by
  simp_rw [not_forall, exists_prop, not_or]
  exists (fun n => ↑(n % 2)), (fun n => ↑(1 - n % 2)); and_intros
  · convert tendsto_const_nhds with n; simp +contextual [Classical.or_iff_not_imp_left]
  all_goals rw [tendsto_iff_seq_tendsto]; simp_rw [not_forall, exists_prop]
  · exists fun n => 2 * n + 1
    use (tendsto_id.const_mul_atTop' two_pos).atTop_add_nonneg fun n => zero_le_one
    simp [Function.comp_def]
  · exists fun n => 2 * n
    use tendsto_id.const_mul_atTop' two_pos
    simp [Function.comp_def]
