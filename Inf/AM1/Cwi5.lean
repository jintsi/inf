import Inf.AM1.Deriv
import Inf.AM1.Cwi1
import Inf.AM1.Cwi4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace AM1.Cwi5

open Real

theorem Zad1 : HasDerivAt (fun x => sqrt (5 - 2 * x)) (-1 / 3) (-2) := by
  simp [hasDerivAt_iff_hasLimAt', mul_add, ← sub_sub]; norm_num
  apply HasLimAt.of_eventually_eq
  · simp [Eventually]; exists 9 / 2, (by positivity); intro x hx hb; calc
      (√(9 - 2 * x) - 3) / x = (√(9 - 2 * x) + 3) * (√(9 - 2 * x) - 3) / ((√(9 - 2 * x) + 3) * x) := by field
      _ = (9 - 2 * x - 3 ^ 2) / ((√(9 - 2 * x) + 3) * x) := by
        congr; rw [← sq_sub_sq, sq_sqrt]
        grw [lt_of_abs_lt hb]; norm_num
      _ = -2 / (√(9 - 2 * x) + 3) := by field_simp; norm_num
  convert Continuous.hasLimAt ?_ 0; norm_num
  apply (((continuous_mul_left 2).const_sub 9).sqrt.add_const 3).const_div (-2)
  intro x; positivity

open scoped Classical in
/-- This one reuses `AM1.Cwi4.Zad8` to not duplicate proofs. -/
theorem Zad2 {x : ℝ} : DifferentiableAt ℝ (fun x => if Irrational x then 0 else x ^ 2) x ↔ x = 0 := by
  use fun h => Cwi4.Zad8.mp h.continuousAt
  intro h; subst h
  apply HasDerivAt.differentiableAt (f' := 0)
  rw [hasDerivAt_iff_hasLimAt', ← EReal.coe_zero, HasLimAt.def]; simp
  intro e he; exists e, he; intro x hx hb
  split <;> simpa [sq]

theorem Zad3 {x : ℝ} : DifferentiableAt ℝ (fun x => x / (1 + exp (1 / x))) x ↔ x ≠ 0 := by
  constructor
  · contrapose; intro; subst x
    rw [← hasDerivAt_deriv_iff, hasDerivAt_iff_hasLimAt]; simp
    apply forall_not_of_not_exists
    apply mt (Exists.imp fun x => HasLimAt.of_eq (by simp; intro x hx; rw [div_div_cancel_left' hx]))
    apply not_hasLimAt_of_left_ne_right (g₁ := 1) (g₂ := 0) (by simp) (by simp)
    · have h : HasLeftLim (fun x => exp x⁻¹) Set.univ 0 (0 : ℝ) :=
        ((hasLimAt_id 0).inv_zero_neg (by simp [← EReal.coe_zero]; exists 1, zero_lt_one; tauto)).rexp_bot
      convert (h.const_add 1).inv; simp
    · have h : HasRightLim (fun x => exp x⁻¹) Set.univ 0 ⊤ :=
        ((hasLimAt_id 0).inv_zero_pos (by simp [← EReal.coe_zero]; exists 1, zero_lt_one; tauto)).rexp_top
      convert (h.const_add 1).inv (by simp [-EReal.coe_one])
    · simp
  · intro hx; apply DifferentiableAt.fun_div <;> simp [differentiableAt_inv_iff, hx]
    rw [← ne_eq]; positivity

/-- Zad. 5 -/
theorem _root_.Real.hasDerivAt_cot {x : ℝ} (h : sin x ≠ 0) : HasDerivAt cot (-1 / sin x ^ 2) x := by
  rw [funext Real.cot_eq_cos_div_sin]
  convert HasDerivAt.fun_div (Real.hasDerivAt_cos x) (Real.hasDerivAt_sin x) h using 2
  simp [← neg_add', -neg_add_rev, ← sq]

/-- Zad.6 -/
theorem _root_.Real.hasDerivAt_arccot (x : ℝ) : HasDerivAt arccot (-1 / (1 + x ^ 2)) x := by
  rw [← div_neg_eq_neg_div', one_div]
  apply HasDerivAt.of_local_left_inverse (f := cot)
  · exact Real.continuousAt_arctan.const_sub (π / 2)
  · convert hasDerivAt_cot _ using 1 <;> simp [arccot, sin_pi_div_two_sub, cos_sq_arctan, (cos_arctan_pos x).ne']
  · rw [neg_ne_zero]; positivity
  · simp [Metric.eventually_nhds_iff]; exists 1, zero_lt_one; intro y _
    simp [cot_eq_cos_div_sin, arccot, cos_pi_div_two_sub, sin_pi_div_two_sub, ← tan_eq_sin_div_cos]

theorem Zad8 (h : HasDerivAt f f' x) : HasLimAt (fun h => (f (x + h) - f (x - h)) / (2 * h)) Set.univ 0 f' := by
  have h1 := hasDerivAt_iff_hasLimAt'.mp h
  have h2 := HasLimAt.comp_neg.mp h1; simp at h2
  convert (h1.add h2).div_const two_ne_zero using 2
  · ring_nf
  · rw [← EReal.coe_add, ← EReal.coe_div]; simp

theorem Zad9_ne_zero {x : ℝ} (hne : x ≠ 0) :
    HasDerivAt (fun x => x ^ 2 * sin (1 / x)) (2 * x * sin (1 / x) - cos (1 / x)) x := by
  convert (hasDerivAt_pow 2 x).fun_mul (hasDerivAt_inv hne).sin using 1 <;> grind

theorem Zad9_zero : HasDerivAt (fun x => x ^ 2 * sin (1 / x)) 0 0 := by
  simp [hasDerivAt_iff_hasLimAt']
  apply HasLimAt.squeeze (f := fun x => -|x|) (h := abs)
  · apply eventually_true; simp; intro x; rw [show x ^ 2 * sin x⁻¹ / x = x * sin x⁻¹ by field]
    by_cases! hx : 0 ≤ x
    · grw [← Real.neg_one_le_sin]; simp [abs_of_nonneg hx]
    · grw [← le_mul_of_le_one_right hx.le (Real.sin_le_one _)]; simp [abs_of_neg hx]
  · apply eventually_true; simp; intro x; rw [show x ^ 2 * sin x⁻¹ / x = x * sin x⁻¹ by field]
    by_cases! hx : 0 ≤ x
    · grw [Real.sin_le_one]; simp [abs_of_nonneg hx]
    · grw [(mul_le_mul_left_of_neg hx).mpr (Real.neg_one_le_sin _)]; simp [abs_of_neg hx]
  · intro x hx h; convert h.abs.neg; simp [-EReal.coe_zero]
  · intro x hx h; convert h.abs; rw [abs_zero]; rfl

theorem Zad9_not_continuous : ¬Continuous (deriv (fun x => x ^ 2 * sin (1 / x))) := by
  apply mt Continuous.hasLim; push_neg
  use 0, fun n => (n * (2 * π))⁻¹; and_intros
  · convert (HasLim'.id.mul_const (show 2 * π ≠ 0 by positivity)).inv (by simp)
    rw [EReal.top_mul_coe_of_pos (by positivity)]; simp [← EReal.coe_zero]
  · rw [Zad9_zero.deriv, Function.comp_def]
    apply mt (HasLim.of_eventually_eq ?_)
    · apply mt (HasLim.const (-1)).eq; simp
    · exists 1; intro n hn; rw [(Zad9_ne_zero (by positivity)).deriv]; simp
      rw [← mul_assoc _ 2, ← Nat.cast_ofNat, ← Nat.cast_mul, sin_nat_mul_pi, mul_zero, zero_sub]

theorem Zad10 (n : ℕ) : iteratedDeriv n (fun x => x ^ 2 * exp (-x)) =
    fun x => (-1) ^ n * (n * (n-1) * exp (-x) - 2 * n * x * exp (-x) + x ^ 2 * exp (-x)) := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [iteratedDeriv_succ, ih, pow_succ (-1 : ℝ), -neg_mul, neg_mul_comm, -neg_add_rev, neg_add,
      -neg_sub, neg_sub']
    funext x; congr; apply HasDerivAt.deriv
    have h := (hasDerivAt_neg x).exp
    convert ((h.const_mul _).sub (((hasDerivAt_id' x).const_mul _).fun_mul h)).add
      ((hasDerivAt_pow 2 x).mul h) using 1
    ring
