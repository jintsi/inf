import Inf.AM1.LimitAt
import Inf.AM1.Cwi3

namespace AM1.Cwi4

open Real

theorem Zad1 : ¬∃ g, HasRightLim (fun x => sin (x ^ 3)⁻¹) Set.univ 0 g := by
  apply not_hasLimAt_of_ne (x₁ := fun n => (n.succ * π)⁻¹.cbrt) (x₂ := fun n => (π / 2 + n * (2 * π))⁻¹.cbrt)
  · simp [Real.cbrt, WithBot.some, WithTop.some]; intro n; and_intros <;> positivity
  · simp [Real.cbrt, WithBot.some, WithTop.some]; intro n; and_intros <;> positivity
  · simp [Real.cbrt, HasLim']
    convert ((HasLim'.id.top_add_const 1).inv_top.const_mul π⁻¹).pow_const'
      (fun _ => by positivity) (show 0 ≤ 3⁻¹ by positivity); simp
  · simp [Real.cbrt, HasLim']
    convert ((HasLim'.id.top_mul_pos (by positivity) (.const (2 * π))).const_add_top (π / 2)).inv_top.pow_const'
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
