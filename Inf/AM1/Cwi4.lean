import Inf.AM1.Continuous
import Inf.AM1.Cwi3
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Complex.ExponentialBounds

namespace AM1.Cwi4

open Real

theorem Zad1 : ¬∃ g, HasRightLim (fun x => sin (x ^ 3)⁻¹) Set.univ 0 g := by
  apply not_hasLimAt_of_ne (x₁ := fun n => (n.succ * π)⁻¹.cbrt) (x₂ := fun n => (π / 2 + n * (2 * π))⁻¹.cbrt)
  · simp [Real.cbrt]; intro n; and_intros <;> positivity
  · simp [Real.cbrt]; intro n; and_intros <;> positivity
  · simp [Real.cbrt, HasLim']
    convert ((HasLim'.id.add_const 1).const_div π⁻¹ (by simp [-EReal.coe_one])).rpow_const
      (Or.inr <| show 0 ≤ 3⁻¹ by positivity) using 1; simp
  · simp [Real.cbrt, HasLim']
    have H := (HasLim'.id.mul_const (show 2 * π ≠ 0 by simp)).const_add (π / 2)
    simp [EReal.top_mul_of_pos (show (0 : EReal) < (2 : ℝ) * π by norm_cast; simp [Real.pi_pos])] at H
    convert H.inv.rpow_const (Or.inr <| show 0 ≤ 3⁻¹ by positivity); simp
  · refine HasLim'.of_eq (b := fun _ => 0) (g := 0) ?_ (by exact HasLim.const 0)
    intro n; simp [Real.cbrt]; rw [← Nat.cast_ofNat, Real.rpow_inv_natCast_pow] <;> try positivity
    simp [add_mul]
  · refine HasLim'.of_eq (b := fun _ => 1) (g := 1) ?_ (by exact HasLim.const 1)
    intro n; simp [Real.cbrt]; rw [← Nat.cast_ofNat (n := 3), Real.rpow_inv_natCast_pow] <;> try positivity
    simp
  · simp

theorem Zad2a : HasLimAt (fun x => (sqrt (5 - 2 * x) - sqrt (3 - x)) / (x ^ 3 - 8)) Set.univ 2 (-1 / 24 : ℝ) := by
  rw [neg_div, one_div, neg_inv, EReal.coe_inv]
  apply HasLimAt.of_eq (fun x hx hne => (inv_div _ _).symm)
  apply HasLimAt.inv <;> try positivity
  apply HasLimAt.of_eventually_eq (a := 2) ⟨1 / 2, (by simp), fun x _ hne ha => by calc
    (x ^ 3 - 8) / (√(5 - 2 * x) - √(3 - x)) = (x - 2) * (x ^ 2 + x * 2 + 4) / _ := by congr; ring
    _ = _ * (√(5 - 2 * x) + √(3 - x)) / ((5 - 2 * x) - (3 - x)) := by
      simp [abs_lt] at ha
      rw [div_eq_div_iff]; nth_rw 2 [mul_assoc]; congr
      convert sq_sub_sq _ _ <;> rw [Real.sq_sqrt] <;> linarith
      rw [sub_ne_zero, Ne, Real.sqrt_inj]; all_goals grind
    _ = -(x ^ 2 + x * 2 + 4) * (√(5 - 2 * x) + √(3 - x)) := by grind
  ⟩
  have hx : HasLimAt (fun x => x) Set.univ 2 (2 : ℝ) := hasLimAt_id 2
  convert (((hx.pow_const 2).add (hx.mul_const 2) (by norm_cast)).add_const 4).neg.mul
    ((((hx.const_mul 2).const_sub 5).rpow_const (1 / 2)).add
    ((hx.const_sub 3).rpow_const (1 / 2))) (by simp; norm_num; exact fun _ => EReal.coe_ne_top 2) using 1
  · ext; congr <;> apply Real.sqrt_eq_rpow
  · simp [sq]; norm_cast; norm_num

theorem Zad2b : HasLimAt (fun x => sqrt (x ^ 2 + π * x) + x) Set.univ ⊥ (-π / 2 : ℝ) := by
  apply HasLimAt.of_eventually_eq (a := ⊥) ⟨-π, fun x _ hx => by have : x < 0 := (by grw [hx]; simp [pi_pos]); calc
    √(x ^ 2 + π * x) + x = (√(x ^ 2 + π * x) - √(x ^ 2)) * (√(x ^ 2 + π * x) + √(x ^ 2)) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      rw [mul_div_cancel_right₀]
      · rw [sub_eq_add_neg]; simp [sqrt_sq_eq_abs, ← neg_eq_iff_eq_neg]; symm; simp [this.le]
      · apply ne_of_gt; apply add_pos_of_nonneg_of_pos; simp; simp [sq_pos_iff, this.ne]
    _ = (√(x ^ 2 + π * x) ^ 2 - √(x ^ 2) ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by congr; simp [sq_sub_sq, mul_comm]
    _ = (x ^ 2 + π * x - x ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      simp_rw [sub_eq_add_neg]; congr 3 <;> rw [sq_sqrt]; swap; exact sq_nonneg x
      rw [sq, ← add_mul]; apply mul_nonneg_of_nonpos_of_nonpos; repeat linarith
    _ = -π * √(x ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      congr; simp [← mul_neg, sqrt_sq_eq_abs, ← neg_eq_iff_eq_neg]; symm; simp [this.le]
    _ = -π / (√(x ^ 2 + π * x) / √(x ^ 2) + √(x ^ 2) / √(x ^ 2)) := by rw [← add_div, ← div_mul, mul_div_right_comm]
    _ = -π / (√(1 + π / x) + 1) := by
      rw [div_self, ← sqrt_div', add_div, div_self, sq, mul_div_mul_right] <;> simp [sq_nonneg, this.ne]
  ⟩
  convert hasLimAt_id ⊥ |>.const_div π |>.const_add 1 |>.rpow_const (1 / 2) ?_
    |>.add_const 1 |>.const_div (-π) (by positivity) using 4 <;> simp [sqrt_eq_rpow]; norm_cast

theorem Zad2c : HasLimAt (fun x => (sin x + cos x) / cos (2 * x)) Set.univ (-π / 4 : ℝ) (sqrt 2 / 2 : ℝ) := by
  simp [cos_two_mul', sq_sub_sq, add_comm, ← div_div]
  apply HasLimAt.of_eventually_eq (h := fun x => 1 / (cos x - sin x)) ?_
  · convert ((continuous_cos.sub continuous_sin).hasLimAt (-π / 4)).const_div 1 (by simp [neg_div])
    simp [neg_div, ← EReal.coe_inv]; exact sqrt_div_self
  exists π / 4, by simp [pi_pos]
  intro x _ hne hd
  rw [abs_lt] at hd; simp [neg_div, ← sub_lt_iff_lt_add] at hd; ring_nf at hd
  congr; apply div_self
  rw [Ne, add_eq_zero_iff_eq_neg, ← cos_add_pi_div_two, ← Ne, ← sub_ne_zero, cos_sub_cos]
  simp; and_intros <;> rw [sin_eq_zero_iff_of_lt_of_lt] <;> bound

theorem Zad4 {D : Set ℝ} (f : ℝ → ℝ) (m k : ℝ) : HasLimAt (fun x => f x - (m * x + k)) D ⊤ 0 ↔
    HasLimAt (fun x => f x / x) D ⊤ m ∧ HasLimAt (fun x => f x - m * x) D ⊤ k := by
  constructor
  · intro h
    apply HasLimAt.add_const k at h; simp [← sub_sub] at h
    rw [and_iff_left (by assumption)]
    replace h := (h.div (hasLimAt_id ⊤)).add_const m
    simp [sub_div] at h
    exact h.of_eventually_eq ⟨0, fun x _ hx => by simp [mul_div_cancel_right₀ m hx.ne']⟩
  · intro ⟨_, h⟩
    convert h.sub_const k using 2 <;> simp [sub_sub]

open Classical in
theorem Zad8 {x : ℝ} : ContinuousAt (fun x => if Irrational x then 0 else x ^ 2) x ↔ x = 0 := by
  constructor
  · simp [continuousAt_iff_hasLim]; intro h
    let xq := fun (n : ℕ) => ⌊x * n⌋ / (n : ℝ)
    let xnq := fun (n : ℕ) => xq n + √2 / n
    have h1 : HasLim xq x := by
      apply HasLim.squeeze_const (a := fun n => x - 1 / n)
      · exists 1; intro n hn; subst xq; simp; grw [← Int.sub_one_lt_floor]; simp [sub_div]
        rw [mul_div_cancel_right₀]; positivity
      · exists 1; intro n hn; subst xq; simp; grw [Int.floor_le]; rw [mul_div_cancel_right₀]; positivity
      · convert HasLim'.id.inv.const_sub x; simp
    have h2 : HasLim xnq x := by
      convert h1.add (HasLim'.id.inv.const_mul (show √2 ≠ 0 by simp)) using 1; simp
    have h3 : HasLim ((fun x => if Irrational x then 0 else x ^ 2) ∘ xq) (x ^ 2) := by
      apply HasLim.of_eventually_eq ⟨1, fun n hn => by
        apply ite_cond_eq_false; simp [irrational_iff_ne_rational]; exists ⌊x * n⌋, n; and_intros
        positivity; rfl⟩
      simp [sq]; exact h1.mul h1
    have h4 : HasLim ((fun x => if Irrational x then 0 else x ^ 2) ∘ xnq) 0 :=
      HasLim.of_eventually_eq ⟨1, fun n hn => by
        apply ite_cond_eq_true; subst xnq; simp; rw [show xq n = (⌊x * n⌋ / n : ℚ) by simp; rfl]
        simp [-Rat.cast_div, irrational_sqrt_two]; positivity⟩ (HasLim.const 0)
    replace h1 := (h xq h1).eq h3; replace h2 := (h xnq h2).eq h4
    rw [h1, sq_eq_zero_iff] at h2; assumption
  · intro h; subst h; simp [Metric.continuousAt_iff]
    intro e he; exists sqrt e, (by simpa); intro x hb
    split <;> simpa [sq_lt, ← abs_lt]

theorem Zad9 : ∃ x ∈ Set.Ioo 0 1, exp (-x) = sin (π * x / 2) := by
  have h := intermediate_value_Ioo' zero_le_one ((Continuous.rexp continuous_neg).sub
    (Real.continuous_sin.comp' ((continuous_mul_left π).div_const 2))).continuousOn
  simp [Set.subset_def] at h
  convert h 0 (by grw [exp_neg_one_lt_half]; norm_num) zero_lt_one using 3
  exact sub_eq_zero.symm

theorem Zad11 : UniformContinuous NNReal.sqrt ∧ ¬∃ K, LipschitzWith K NNReal.sqrt := by
  and_intros
  · simp [Metric.uniformContinuous_iff, NNReal.dist_eq]
    intro e he; exists e ^ 2, sq_pos_of_pos he
    intro ⟨a, ha⟩ ⟨b, hb⟩ h; simp at *
    wlog hab : b ≤ a generalizing a b
    · rw [abs_sub_comm]; rw [abs_sub_comm] at h; exact this b hb a ha h (le_of_not_ge hab)
    rw [← abs_of_pos he, ← sq_lt_sq]; apply h.trans_le'
    simp [sub_sq, abs_of_nonneg (sub_nonneg_of_le hab), *, sub_add, le_sub_iff_add_le, ← two_mul, mul_assoc]
    grw [← Real.sqrt_le_sqrt hab]; simp [hb]
  · simp [lipschitzWith_iff_dist_le_mul]
    intro K; exists 0; simp [NNReal.dist_eq]
    by_cases hK : K = 0
    · exists 1; subst K; simp
    · exists 1 / (2 * K) ^ 2; simp; field_simp; simp
