import Inf.AM1.Cwi1
import Inf.AM1.Cwi4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace AM1.Cwi5

open Real Topology Filter

theorem Zad1 : HasDerivAt (fun x => √(5 - 2 * x)) (-1 / 3) (-2) := by
  simp_rw [hasDerivAt_iff_tendsto_slope_zero, smul_eq_mul, mul_add, ← sub_sub]; norm_num
  apply Tendsto.congr' (f₁ := fun x => -2 / (√(9 - 2 * x) + 3))
  · rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 9 / 2, (by simp); simp; grind
  apply tendsto_nhdsWithin_of_tendsto_nhds
  convert ContinuousAt.tendsto ?_ using 2; · norm_num
  fun_prop (disch := norm_num)

open scoped Classical in
/-- This one reuses `AM1.Cwi4.Zad8` to not duplicate proofs. -/
theorem Zad2 {x : ℝ} : DifferentiableAt ℝ (fun x => if Irrational x then 0 else x ^ 2) x ↔ x = 0 := by
  use fun h => Cwi4.Zad8.mp h.continuousAt
  intro h; subst h
  apply HasDerivAt.differentiableAt (f' := 0)
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro e he; exists e, he; intro x hx hb
  split <;> simp_all [sq]

theorem Zad3 {x : ℝ} : DifferentiableAt ℝ (fun x => x / (1 + (1 / x).exp)) x ↔ x ≠ 0 := by
  constructor
  · contrapose; intro; subst x
    rw [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope, slope_fun_def_field]; ring_nf
    apply mt (Tendsto.congr' ?_ (f₂ := fun x => (1 + x⁻¹.exp)⁻¹)); swap
    · apply eventuallyEq_nhdsWithin_of_eqOn; grind [Set.EqOn]
    intro h
    have hl : Tendsto (fun x : ℝ => (1 + x⁻¹.exp)⁻¹) (𝓝[<] 0) (𝓝 1) := by
      convert ((tendsto_exp_comp_nhds_zero.mpr tendsto_inv_nhdsLT_zero).const_add 1).inv₀
      simp
    have hr : Tendsto (fun x : ℝ => (1 + x⁻¹.exp)⁻¹) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_inv_nhdsGT_zero)).inv_tendsto_atTop
    exact one_ne_zero <| (tendsto_nhds_unique hl (tendsto_nhdsWithin_mono_left (by simp) h)).trans
      (tendsto_nhds_unique (tendsto_nhdsWithin_mono_left (by simp) h) hr)
  · intro hx; fun_prop (disch := positivity)

/-- Zad. 5 -/
theorem _root_.Real.hasDerivAt_cot {x : ℝ} (h : sin x ≠ 0) : HasDerivAt cot (-1 / sin x ^ 2) x := by
  rw [funext Real.cot_eq_cos_div_sin]
  convert HasDerivAt.fun_div (Real.hasDerivAt_cos x) (Real.hasDerivAt_sin x) h using 2
  simp [← neg_add', -neg_add_rev, ← sq]

/-- Zad.6 -/
theorem _root_.Real.hasDerivAt_arccot (x : ℝ) : HasDerivAt arccot (-1 / (1 + x ^ 2)) x := by
  rw [← div_neg_eq_neg_div', one_div]
  apply HasDerivAt.of_local_left_inverse (f := cot)
  · fun_prop [Real.arccot]
  · convert hasDerivAt_cot _ using 1
      <;> simp [arccot, sin_pi_div_two_sub, cos_sq_arctan, (cos_arctan_pos x).ne']
  · rw [neg_ne_zero]; positivity
  · rw [Metric.eventually_nhds_iff]; exists 1, zero_lt_one; intro y _
    simp [cot_eq_cos_div_sin, arccot, cos_pi_div_two_sub, sin_pi_div_two_sub, ← tan_eq_sin_div_cos]

theorem Zad8 {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) :
    Tendsto (fun h => (f (x + h) - f (x - h)) / (2 * h)) (𝓝[≠] 0) (𝓝 f') := by
  have h1 := h.tendsto_slope_zero
  convert (h1.add (h1.comp (f := Neg.neg) ?_)).div_const 2 using 2 <;> try grind [smul_eq_mul]
  rw [tendsto_nhdsWithin_iff]; and_intros
  · convert tendsto_nhdsWithin_of_tendsto_nhds (tendsto_neg (0 : ℝ)); exact neg_zero.symm
  · apply eventually_nhdsWithin_of_forall; simp

theorem Zad9_ne_zero {x : ℝ} (hne : x ≠ 0) :
    HasDerivAt (fun x => x ^ 2 * sin (1 / x)) (2 * x * sin (1 / x) - cos (1 / x)) x := by
  convert (hasDerivAt_pow 2 x).fun_mul (hasDerivAt_inv hne).sin using 1 <;> grind

theorem Zad9_zero : HasDerivAt (fun x => x ^ 2 * sin (1 / x)) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]; ring_nf
  apply Tendsto.congr' (f₁ := fun x => sin x⁻¹ * x)
  · apply eventuallyEq_nhdsWithin_of_eqOn; grind [Set.EqOn]
  apply bdd_le_mul_tendsto_zero' 1
  · simp [abs_sin_le_one]
  · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

theorem Zad9_not_continuous : ¬Continuous (deriv (fun x => x ^ 2 * sin (1 / x))) := by
  apply mt fun h => Continuous.tendsto' h 0 0 Zad9_zero.deriv
  rw [tendsto_iff_seq_tendsto]; push Not; use fun n => (n * (2 * π))⁻¹,
    (tendsto_natCast_atTop_atTop.atTop_mul_const two_pi_pos).inv_tendsto_atTop
  rw [Function.comp_def]; apply mt (Tendsto.congr' ?_); pick_goal 3
  · exact (eventually_ne_atTop 0).mono fun x h => (Zad9_ne_zero (by simpa)).deriv
  simp; simp [← mul_assoc, mul_two, ← Nat.cast_add]

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
