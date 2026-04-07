import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace AM1.Cwi8

open Real

theorem Zad1a (h : 0 < x) : HasDerivAt (fun x => log x - 4 / √x - 1 / x) ((√x + 1) ^ 2 / x ^ 2) x := by
  convert (hasDerivAt_log h.ne').fun_sub (((hasDerivAt_sqrt h.ne').fun_inv (by positivity)).const_mul 4)
    |>.fun_sub (hasDerivAt_inv h.ne') using 1
  · ext x; simp [div_eq_mul_inv]
  · rw [sq_sqrt h.le]; ring_nf; rw [sq_sqrt h.le]; field_simp; ring_nf; rw [sq_sqrt h.le]

theorem Zad1b (h : x ≠ 0) : HasDerivAt (fun x => log x ^ 8 / 8) (log x ^ 7 / x) x := by
  convert ((hasDerivAt_log h).fun_pow 8).div_const 8 using 1; field

theorem Zad1c (x : ℝ) : HasDerivAt (fun x => arctan (x ^ 3) / 3) (x ^ 2 / (x ^ 6 + 1)) x := by
  convert (hasDerivAt_pow 3 x).arctan.div_const 3 using 1; field

theorem Zad1d (h₁ : sin x ≠ 0) (h₂ : cos x ≠ 0) : HasDerivAt (fun x => tan x - cot x)
    (sin x ^ 2 * cos x ^ 2)⁻¹ x := by
  have h₃ : tan x ≠ 0 := by rwa [Ne, tan_eq_zero_iff' h₂, ← sin_eq_zero_iff]
  convert (hasDerivAt_tan h₂).fun_sub ((hasDerivAt_tan h₂).fun_inv h₃) using 1
  · simp
  · rw [tan_eq_sin_div_cos]; field_simp; simp

theorem Zad1e (x : ℝ) : HasDerivAt (fun x => ((x ^ 2 + 1) * arctan x - x) / 2) (x * arctan x) x := by
  convert ((((hasDerivAt_pow 2 x).add_const 1).fun_mul (hasDerivAt_arctan x)).fun_sub
    (hasDerivAt_id' x)).div_const 2 using 1
  field

theorem Zad1f (x : ℝ) : HasDerivAt (fun x => -(2 ^ (-sin x ^ 2) / log 2))
    (2 ^ (-sin x ^ 2) * sin (2 * x)) x := by
  convert ((((hasDerivAt_sin x).fun_pow 2).fun_neg.const_rpow two_pos).div_const (log 2)).neg using 1
  rw [sin_two_mul]; field

alias Zad1g := hasDerivAt_arcsin

theorem Zad1h (h : -1 ≠ x) : HasDerivAt (fun x => (1 + x ^ 5) * (log (1 + x ^ 5) - 1) / 5)
    (x ^ 4 * log (1 + x ^ 5)) x := by
  have h : 1 + x ^ 5 ≠ 0 := by
    rw [add_comm, ← sub_neg_eq_add, sub_ne_zero, ne_comm]
    convert (show Odd 5 by decide).pow_inj.ne.mpr h; norm_num
  have := by simpa [-hasDerivAt_const_add_iff] using ((hasDerivAt_pow 5 x).const_add 1)
  convert (this.fun_mul ((this.log h).sub_const 1)).div_const 5 using 1
  field

theorem Zad1i (x : ℝ) : HasDerivAt (fun x => -(exp (-x) * (2 * cos (2 * x) + sin (2 * x)) / 5))
    (exp (-x) * sin (2 * x)) x := by
  convert (hasDerivAt_neg x).exp.fun_mul (((hasDerivAt_const_mul 2).cos.const_mul 2).fun_add
    (hasDerivAt_const_mul 2).sin) |>.div_const 5 |>.fun_neg using 1
  ring

theorem Zad1j (h₀ : sin x ≠ 0) (h₁ : sin x ≠ 1) (h₂ : sin x ≠ -1) :
    HasDerivAt (fun x => log (-log (sin x))) (cot x / log (sin x)) x := by
  simp_rw [log_neg_eq_log, cot_eq_cos_div_sin]
  apply ((hasDerivAt_sin x).log h₀).log
  simp; bound

theorem Zad1k (x : ℝ) : HasDerivAt (fun x => arctan (exp x)) (exp x + exp (-x))⁻¹ x := by
  convert (hasDerivAt_exp x).arctan using 1; rw [exp_neg]; field

theorem Zad1l (x : ℝ) : HasDerivAt (fun x => 2 * arctan ((2 * x + 1) / √3) / √3) (x ^ 2 + x + 1)⁻¹ x := by
  convert (((hasDerivAt_const_mul 2).add_const 1).div_const √3).arctan.mul_const (2 / √3) using 1
  · ext; ring
  · field_simp; rw [sq_sqrt (by simp), div_eq_iff]; · ring
    ring_nf; nlinarith

theorem _root_.hasDerivAt_log_add_const {x C : ℝ} (h : x ≠ -C) :
    HasDerivAt (fun x => log (x + C)) (x + C)⁻¹ x := by
  simpa using ((hasDerivAt_id' x).add_const C).log (by bound)

theorem _root_.hasDerivAt_log_sub_const {x C : ℝ} (h : x ≠ C) :
    HasDerivAt (fun x => log (x - C)) (x - C)⁻¹ x := by
  simpa using ((hasDerivAt_id' x).sub_const C).log (by bound)

theorem Zad2a (h₁ : x ≠ 1) (h₂ : x ≠ -1) :
    HasDerivAt (fun x => (log (x + 1) - log (x - 1)) / 2) (1 - x ^ 2)⁻¹ x := by
  convert ((hasDerivAt_log_add_const h₂).fun_sub (hasDerivAt_log_sub_const h₁)).div_const 2 using 1
  field (disch := grind)

theorem Zad2b (h₀ : x ≠ 0) (h₂ : x ≠ 2) (h₃ : x ≠ 3) :
    HasDerivAt (fun x => x + log x / 6 - 9 / 2 * log (x - 2) + 28 / 3 * log (x - 3))
    ((x ^ 3 + 1) / (x ^ 3 - 5 * x ^ 2 + 6 * x)) x := by
  convert (hasDerivAt_id' x).fun_add ((hasDerivAt_log h₀).div_const 6)
    |>.fun_sub ((hasDerivAt_log_sub_const h₂).const_mul (9 / 2))
    |>.fun_add ((hasDerivAt_log_sub_const h₃).const_mul (28 / 3)) using 1
  field (disch := grind)

theorem Zad2c (h₁ : x ≠ 1) (h₂ : x ≠ -2) : HasDerivAt
    (fun x => -(3 * (x - 1))⁻¹ + 2 / 9 * log (x - 1) - 2 / 9 * log (x + 2)) (x / (2 - 3 * x + x ^ 3)) x := by
  convert ((((hasDerivAt_id' x).sub_const 1).const_mul 3).fun_inv (by bound)).fun_neg
    |>.fun_add ((hasDerivAt_log_sub_const h₁).const_mul (2 / 9))
    |>.fun_sub ((hasDerivAt_log_add_const h₂).const_mul (2 / 9)) using 1
  field (disch := grind)

theorem Zad2d (h : x ≠ -1) : HasDerivAt
    (fun x => log (x + 1) / 3 - log (x ^ 2 - x + 1) / 6 + arctan ((2 * x - 1) / √3) / √3) (x ^ 3 + 1)⁻¹ x := by
  have : x ^ 2 - x + 1 ≠ 0 := by nlinarith
  convert ((hasDerivAt_log_add_const h).div_const 3).fun_sub
    (((((hasDerivAt_pow 2 x).fun_sub (hasDerivAt_id' x)).add_const 1).log this).div_const 6)
    |>.fun_add ((((hasDerivAt_const_mul 2).sub_const 1).div_const √3).arctan.div_const √3) using 1
  field_simp (disch := grind); rw [sq_sqrt (3).ofNat_nonneg]; ring

theorem Zad3_step (n : ℕ) (ih : HasDerivAt f (sin x ^ n) x) :
    HasDerivAt (fun x => ((n + 1) * f x - sin x ^ (n + 1) * cos x) / (n + 2)) (sin x ^ (n + 2)) x := by
  convert (ih.const_mul ↑(n + 1)).fun_sub (((hasDerivAt_sin x).fun_pow (n + 1)).fun_mul (hasDerivAt_cos x))
    |>.div_const (n + 2)
  · exact (Nat.cast_add_one n).symm
  · rw [mul_assoc, ← sq, cos_sq']; push_cast; field

theorem _root_.HasDerivAt.tan {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hx : cos (f x) ≠ 0) :
    HasDerivAt (fun x => tan (f x)) (f' / cos (f x) ^ 2) x := by
  convert (hasDerivAt_tan hx).comp x hf using 1; ring

theorem Zad4a (h : cos (x / 2) ≠ 0) : HasDerivAt (fun x => arctan (2 * tan (x / 2)) / 2)
    (5 - 3 * cos x)⁻¹ x := by
  convert (((hasDerivAt_mul_const 2⁻¹).tan h).const_mul 2).arctan.div_const 2 using 1
  have : 5 - 3 * cos x ≠ 0 := by apply ne_of_gt; grw [cos_le_one]; norm_num
  rw [tan_eq_sin_div_cos]; field_simp; norm_num
  rw [← mul_div_cancel₀ x two_ne_zero, cos_two_mul, mul_div_cancel_left₀ (x / 2) two_ne_zero]
  ring_nf; apply eq_sub_of_add_eq; ring_nf; simp [← add_mul]

theorem Zad4b (h : cos x ≠ -1) : HasDerivAt (fun x => tan (x / 2) + 6 * log (cos (x / 2)))
    ((1 - 3 * sin x) / (1 + cos x)) x := by
  have : cos (x / 2) ≠ 0 := by
    rw [ne_eq, cos_eq_zero_iff]; rw [ne_eq, cos_eq_neg_one_iff] at h; convert h using 3; grind
  convert ((hasDerivAt_mul_const 2⁻¹).tan this).fun_add
    (((hasDerivAt_mul_const 2⁻¹).cos.log this).const_mul 6) using 1
  field_simp
  rw [← mul_div_cancel₀ x two_ne_zero, sin_two_mul, cos_two_mul, mul_div_cancel_left₀ _ two_ne_zero]
  field

theorem Zad4c (h₀ : 0 < x) (h₁ : x < 1) :
    HasDerivAt (fun x => 2 * (arctan √(x⁻¹ - 1) - √(x⁻¹ - 1))) (x⁻¹ * √(x⁻¹ - 1)) x := by
  have h : 0 < x⁻¹ - 1 := by bound [(one_lt_inv₀ h₀).mpr h₁]
  have := ((hasDerivAt_inv h₀.ne').sub_const 1).sqrt h.ne'
  convert (this.arctan.fun_sub this).const_mul 2 using 1
  field_simp (disch := grind); rw [sq_sqrt (by grind)]; field
