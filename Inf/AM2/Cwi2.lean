import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Inf.AM1.Cwi8
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

open Topology Filter Real intervalIntegral

namespace AM2.Cwi2

theorem Zad1a : ¬IntervalIntegrable (fun x => (x * log x)⁻¹) MeasureTheory.volume 1 √(exp 1) := by
  rw [show √(exp 1) = exp 2⁻¹ by simp [sqrt_eq_rpow]]
  apply not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    (f := fun x => log (log x)) (𝓝[>] 1) (by simp [Icc_mem_nhdsGT])
  · apply eventually_nhdsWithin_of_forall; simp_rw [Set.mem_Ioi]
    exact fun x hx => (differentiableAt_log (by bound)).log (by simp; bound)
  · apply tendsto_abs_atBot_atTop.comp; apply tendsto_log_nhdsNE_zero.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · convert tendsto_nhdsWithin_of_tendsto_nhds (continuousAt_log one_ne_zero).tendsto; simp
    · apply eventually_nhdsWithin_of_forall; simp; bound
  · apply EventuallyEq.isBigO; apply eventually_nhdsWithin_of_forall; simp_rw [Set.mem_Ioi]
    intro x hx; convert deriv.log ?_ ?_ using 1 <;> (simp [div_eq_mul_inv]; bound)

theorem Zad1b : ∫ x in Set.Iic (-2), (1 - x ^ 2)⁻¹ = -(log 3 / 2) := by
  simp_rw [← integral_comp_neg_Ioi, neg_sq,
    show -(log 3 / 2) = 0 - (log (2 + 1) - log (2 - 1)) / 2 by norm_num [neg_div]]
  apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' (g := fun x => (log (x + 1) - log (x - 1)) / 2)
  · simp_rw [Set.mem_Ici]; intro x hx; apply AM1.Cwi8.Zad2a <;> bound
  · simp_rw [Set.mem_Ioi]; intro x hx; simp [le_abs]; bound
  apply Tendsto.congr' (f₁ := fun x => log (1 + 2 / (x - 1)) / 2)
  · rw [EventuallyEq, eventually_atTop]; use 2; intro x hx; rw [← log_div] <;> grind
  convert ((((tendsto_atTop_add_const_right _ (-1) tendsto_id).inv_tendsto_atTop.const_mul 2).const_add 1
    ).log (by simp)).div_const 2 using 2; simp

theorem Zad1c : ∫ x in Set.Ioi 0, exp (-x) * sin (x / 2) = 2 / 5 := by
  rw [show 2 / 5 = 0 - -(2 / 5 * exp (-0) * (2 * sin (0 / 2) + cos (0 / 2))) by simp]
  apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun x => -(2 / 5 * exp (-x) * (2 * sin (x / 2) + cos (x / 2))))
  · intro x hx
    convert DifferentiableAt.hasDerivAt ?_ using 1
    · simp (maxDischargeDepth := 4) [differentiableAt_comp_neg, deriv_comp_neg]; ring
    · fun_prop
  · apply integrable_of_isBigO_exp_neg zero_lt_one (by fun_prop)
    apply Asymptotics.isBigO_of_le
    simpa using fun x => mul_le_of_le_one_right (exp_nonneg (-x)) (abs_sin_le_one (x / 2))
  · have := by simpa using (tendsto_comp_neg_atTop_iff.mpr tendsto_exp_atBot).const_mul (2 / 5)
    convert neg_zero (G := ℝ) ▸ (this.zero_mul_isBoundedUnder_le ?_).neg
    simp [IsBoundedUnder, IsBounded]; use 3, 0; intro x _
    grw [abs_add_le, abs_mul, Nat.abs_ofNat, abs_sin_le_one, abs_cos_le_one]; norm_num

theorem Zad1d : ∫ (x : ℝ), 8 * x / (x ^ 4 + 4 * x ^ 2 + 3) = 0 := by
  have h : ∫ x in Set.Ioi 0, 8 * x / (x ^ 4 + 4 * x ^ 2 + 3) = 0 - (2 * log (1 - 2 / (0 ^ 2 + 3))) := by
    apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun x => 2 * log (1 - 2 / (x ^ 2 + 3)))
    · intro x _;
      convert ((((((hasDerivAt_pow 2 x).add_const 3).fun_inv (by positivity)).const_mul 2).const_sub 1
        ).log (by field_simp; apply div_ne_zero <;> nlinarith)).const_mul 2 using 1
      field (disch := nlinarith)
    · simp_rw [Set.mem_Ioi]; bound
    · convert (((tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ ?_)).const_sub _
        ).log ?_).const_mul _ <;> simp
  have h2 : ∫ x in Set.Iic 0, 8 * x / (x ^ 4 + 4 * x ^ 2 + 3) = (2 * log (1 - 2 / (0 ^ 2 + 3))) := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]; ring_nf at *; rw [MeasureTheory.integral_neg, h, neg_neg]
  rw [← integral_Iic_add_Ioi, h, h2, add_sub_cancel] <;> apply MeasureTheory.Integrable.of_integral_ne_zero
   <;> norm_num [h, h2]

theorem Zad1e : ¬IntervalIntegrable (fun x => x / (1 - x ^ 2)) MeasureTheory.volume 0 2 := by
  apply mt fun h => h.const_mul (-2)
  rw [intervalIntegrable_congr_ae (g := fun x => (x - 1)⁻¹ + (x - -1)⁻¹)]; swap
  · rw [MeasureTheory.aeEq_iff]; simp; convert volume_singleton (a := 1); grind
  apply mt fun h => h.sub ((intervalIntegrable_sub_inv_iff (c := -1)).mpr (by simp))
  simp

theorem Zad1f : ∫ x in 0..1, 1 / √(x - x ^ 2) = π := calc ∫ x in 0..1, 1 / √(x - x ^ 2)
  _ = 2 * ∫ x in 0..1, (2 * √(x - x ^ 2))⁻¹ := by simp_rw [mul_inv, integral_const_mul]; ring_nf
  _ = 2 * ∫ x in 0..1, 1 / √(2 ^ 2 * (x - x ^ 2)) := by simp
  _ = 2 * ∫ x in 0..1, 1 / √(1 - (2 * x - 1) ^ 2) := by ring_nf
  _ = ∫ x in -1..1, deriv arcsin x := by
    rw [mul_integral_comp_mul_sub (f := fun x => 1 / √(1 - x ^ 2))]; norm_num
  _ = arcsin 1 - arcsin (-1) := integral_deriv_eq_sub_uIoo (by fun_prop)
    (by simp [differentiableAt_arcsin]; grind) (monotone_arcsin.monotoneOn _).intervalIntegrable_deriv
  _ = π := by simp
