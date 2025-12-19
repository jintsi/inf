import Inf.AM1.Continuous
import Inf.AM1.Cwi3

namespace AM1.Cwi4

open Real

theorem Zad1 : ¬∃ g, HasRightLim (fun x => sin (x ^ 3)⁻¹) Set.univ 0 g := by
  apply not_hasLimAt_of_ne (x₁ := fun n => (n.succ * π)⁻¹.cbrt) (x₂ := fun n => (π / 2 + n * (2 * π))⁻¹.cbrt)
  · simp [Real.cbrt, WithBot.some, WithTop.some]; intro n; and_intros <;> positivity
  · simp [Real.cbrt, WithBot.some, WithTop.some]; intro n; and_intros <;> positivity
  · simp [Real.cbrt, HasLim']
    convert ((HasLim'.id.top_add_const 1).inv_top.const_mul π⁻¹).rpow_const'
      (fun _ => by positivity) (show 0 ≤ 3⁻¹ by positivity); simp
  · simp [Real.cbrt, HasLim']
    convert ((HasLim'.id.top_mul_pos (by positivity) (.const (2 * π))).const_add_top (π / 2)).inv_top.rpow_const'
      (fun _ => by positivity) (show 0 ≤ 3⁻¹ by positivity); simp
  · refine HasLim'.of_eq (b := fun _ => 0) (g := 0) ?_ (by exact HasLim.const 0)
    intro n; simp [Real.cbrt]; rw [← Nat.cast_ofNat, Real.rpow_inv_natCast_pow] <;> try positivity
    simp [add_mul]
  · refine HasLim'.of_eq (b := fun _ => 1) (g := 1) ?_ (by exact HasLim.const 1)
    intro n; simp [Real.cbrt]; rw [← Nat.cast_ofNat (n := 3), Real.rpow_inv_natCast_pow] <;> try positivity
    simp
  · simp

theorem Zad2a : HasLimAt (fun x => (sqrt (5 - 2 * x) - sqrt (3 - x)) / (x ^ 3 - 8)) Set.univ 2 (-1 / 24 : ℝ) := by
  rw [neg_div, one_div, neg_inv]; apply HasLimAt.of_eq (fun x hx hne => (inv_div _ _).symm)
  apply HasLimAt.inv <;> try positivity
  have hin : (2 : ℝ) ∈ Set.Ioo (3 / 2) (5 / 2) := by norm_num
  apply HasLimAt.of_eq' hin (fun x ⟨_, hl, hu⟩ hne => by calc
    (x ^ 3 - 8) / (√(5 - 2 * x) - √(3 - x)) = (x - 2) * (x ^ 2 + x * 2 + 4) / _ := by congr; ring
    _ = _ * (√(5 - 2 * x) + √(3 - x)) / ((5 - 2 * x) - (3 - x)) := by
      rw [div_eq_div_iff]; nth_rw 2 [mul_assoc]; congr; convert sq_sub_sq _ _ <;> rw [Real.sq_sqrt] <;> linarith
      rw [sub_ne_zero, Ne, Real.sqrt_inj]; all_goals grind
    _ = -(x ^ 2 + x * 2 + 4) * (√(5 - 2 * x) + √(3 - x)) := by grind
  )
  have hx := hasLimAt_id (D := Set.univ) (2 : EReal)
  convert (((hx.pow_const 2).add (hx.mul_const 2)).add_const 4).neg.mul
    ((((hx.const_mul 2).const_sub 5).rpow_const hin (by grind) (inv_nonneg.mpr zero_le_two)).add
    ((hx.const_sub 3).rpow_const hin (by grind) (inv_nonneg.mpr zero_le_two))) using 1
  · simp [Real.sqrt_eq_rpow]
  · norm_num

theorem Zad2b : HasLimAt (fun x => sqrt (x ^ 2 + π * x) + x) Set.univ ⊥ (-π / 2 : ℝ) := by
  apply HasLimAt.of_eq_bot (-π) (fun x hx => by have : x < 0 := (by simp at hx; grw [hx]; simp [pi_pos]); calc
    √(x ^ 2 + π * x) + x = (√(x ^ 2 + π * x) - √(x ^ 2)) * (√(x ^ 2 + π * x) + √(x ^ 2)) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      simp at hx; rw [mul_div_cancel_right₀]
      · rw [sub_eq_add_neg]; simp [sqrt_sq_eq_abs, ← neg_eq_iff_eq_neg]; symm; simp [this.le]
      · apply ne_of_gt; apply add_pos_of_nonneg_of_pos; simp; simp [sq_pos_iff, this.ne]
    _ = (√(x ^ 2 + π * x) ^ 2 - √(x ^ 2) ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by congr; simp [sq_sub_sq, mul_comm]
    _ = (x ^ 2 + π * x - x ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      simp_rw [sub_eq_add_neg]; congr 3 <;> rw [sq_sqrt]; swap; exact sq_nonneg x
      rw [sq, ← add_mul]; apply mul_nonneg_of_nonpos_of_nonpos; simp at hx; repeat linarith
    _ = -π * √(x ^ 2) / (√(x ^ 2 + π * x) + √(x ^ 2)) := by
      congr; simp [← mul_neg, sqrt_sq_eq_abs, ← neg_eq_iff_eq_neg]; symm; simp [this.le]
    _ = -π / (√(x ^ 2 + π * x) / √(x ^ 2) + √(x ^ 2) / √(x ^ 2)) := by rw [← add_div, ← div_mul, mul_div_right_comm]
    _ = -π / (√(1 + π / x) + 1) := by
      rw [div_self, ← sqrt_div', add_div, div_self, sq, mul_div_mul_right] <;> simp [sq_nonneg, this.ne]
  )
  convert hasLimAt_id ⊥ |>.const_div_bot π |>.const_add 1 |>.rpow_const_bot (-π) ?_ one_half_pos.le
    |>.add_const 1 |>.const_div (-π) (by positivity) using 4 <;> simp [sqrt_eq_rpow]; norm_num
  intro x hx; rw [div_eq_mul_inv]; rw [← inv_lt_inv_of_neg] at hx; grw [← hx]; simp
  simp [pi_pos]; grw [hx]; simp [pi_pos]

theorem Zad2c : HasLimAt (fun x => (sin x + cos x) / cos (2 * x)) Set.univ (-π / 4 : ℝ) (sqrt 2 / 2 : ℝ) := by
  simp [cos_two_mul', sq_sub_sq, add_comm, ← div_div]
  have hin : -π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simp [neg_div, neg_lt_iff_pos_add]; and_intros
    · apply div_lt_div_of_pos_left <;> norm_num; exact pi_pos
    · positivity
  apply HasLimAt.of_eq' hin fun x ⟨_, hl, hu⟩ hne => show _ = 1 / (cos x - sin x) by
    congr; apply div_self
    simp [add_eq_zero_iff_eq_neg, ← cos_add_pi_div_two]; apply sub_ne_zero.mp
    rw [cos_sub_cos]; simp; and_intros <;> rw [sin_eq_zero_iff_of_lt_of_lt] <;> try grind
    · ring_nf; grw [← hl]; field_simp; norm_num
    · ring_nf; grw [hu]; field_simp; norm_num
    · field_simp; norm_num
    · field_simp; norm_num
  convert ((continuous_cos.sub continuous_sin).hasLimAt (-π / 4)).const_div 1 ?_ using 3
  · simp [neg_div]; exact sqrt_div_self
  · simp [neg_div]

/-! ...i'm starting to think maybe the whole `HasLimAt` was a bad idea lol -/

open Classical in
theorem Zad8 (x : ℝ) : ContinuousAt (fun x => if Irrational x then 0 else x ^ 2) x ↔ x = 0 := by
  constructor
  · simp [continuousAt_iff_hasLim]; intro h
    let xq := fun (n : ℕ) => ⌊x * n⌋ / (n : ℝ)
    let xnq := fun (n : ℕ) => xq n + √2 / n
    have h1 : HasLim xq x := by
      apply HasLim.squeeze_const (a := fun n => x - 1 / n)
      · exists 1; intro n hn; subst xq; simp; grw [← Int.sub_one_lt_floor]; simp [sub_div]
        rw [mul_div_cancel_right₀]; positivity
      · exists 1; intro n hn; subst xq; simp; grw [Int.floor_le]; rw [mul_div_cancel_right₀]; positivity
      · convert HasLim'.id.inv_top.const_sub x; ext; simp; simp
    have h2 : HasLim xnq x := by convert h1.add (HasLim'.id.inv_top.const_mul √2) using 1; simp
    have h3 : HasLim ((fun x => if Irrational x then 0 else x ^ 2) ∘ xq) (x ^ 2) := by
      apply HasLim.of_eventually_eq ⟨1, fun n hn => by
        apply ite_cond_eq_false; simp [irrational_iff_ne_rational]; exists ⌊x * n⌋, n; and_intros
        positivity; rfl⟩
      simp [sq]; exact h1.mul h1
    have h4 : HasLim ((fun x => if Irrational x then 0 else x ^ 2) ∘ xnq) 0 := by
      apply HasLim.of_eventually_eq ⟨1, fun n hn => by
        apply ite_cond_eq_true; subst xnq; simp; rw [show xq n = (⌊x * n⌋ / n : ℚ) by simp; rfl]
        simp [-Rat.cast_div, irrational_sqrt_two]; positivity⟩; exact HasLim.const 0
    replace h1 := (h xq h1).eq h3; replace h2 := (h xnq h2).eq h4
    rw [h1, sq_eq_zero_iff] at h2; assumption
  · intro h; subst h; simp [Metric.continuousAt_iff]
    intro e he; exists sqrt e, (by simpa); intro x hb
    split <;> simpa [sq_lt, ← abs_lt]
