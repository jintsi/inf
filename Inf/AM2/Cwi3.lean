import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # More of a stub really -/

open MeasureTheory Real

namespace AM2.Cwi3

theorem Zad1a_bounds {x : ℝ} : x ^ 2 / 2 ≤ (x ^ 2 + 1)⁻¹ ↔ x ∈ Set.Icc (-1) 1 := calc
  x ^ 2 / 2 ≤ (x ^ 2 + 1)⁻¹ ↔ (x ^ 2 + 1 / 2) ^ 2 ≤ (3 / 2) ^ 2 := by field_simp; grind
  _ ↔ x ^ 2 + 1 / 2 ≤ 3 / 2 := by rw [sq_le_sq]; congr! 1 <;> (simp; positivity)
  _ ↔ x ^ 2 ≤ 1 := by constructor <;> (intro h; linarith)
  _ ↔ x ∈ Set.Icc (-1) 1 := by simp [abs_le]

theorem Zad1a : volume (regionBetween (fun x => x ^ 2 / 2) (fun x => (x ^ 2 + 1)⁻¹) (Set.Icc (-1) 1))
    = NNReal.pi / 2 - 1 / 3 := calc
  volume (regionBetween (fun x => x ^ 2 / 2) (fun x => (x ^ 2 + 1)⁻¹) (Set.Icc (-1) 1))
  _ = .ofReal (∫ x in Set.Icc (-1) 1, (x ^ 2 + 1)⁻¹ - x ^ 2 / 2) :=
    volume_regionBetween_eq_integral (Continuous.integrableOn_Icc (by fun_prop))
      (Continuous.integrableOn_Icc (by fun_prop (disch := intro x; positivity)))
      measurableSet_Icc fun x => Zad1a_bounds.mpr
  _ = .ofReal (∫ x in -1..1, (x ^ 2 + 1)⁻¹ - x ^ 2 / 2) := by
    rw [intervalIntegral.integral_of_le (by simp), integral_Icc_eq_integral_Ioc]
  _ = .ofReal ((∫ x in -1..1, (x ^ 2 + 1)⁻¹) - ∫ x in -1..1, x ^ 2 / 2) := by
    rw [intervalIntegral.integral_sub] <;> apply Continuous.intervalIntegrable <;>
      fun_prop (disch := intro x; positivity)
  _ = .ofReal (π / 2 - 1 / 3) := by simp [← add_comm (1 : ℝ)]; ring_nf
  _ = NNReal.pi / 2 - 1 / 3 := by
    rw [ENNReal.ofReal_sub, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_eq_coe_nnreal pi_nonneg] <;> simp; rfl

@[simp]
lemma _root_.integral_arctan : ∫ x in a..b, arctan x =
    b * arctan b - log (1 + b ^ 2) / 2 - (a * arctan a - log (1 + a ^ 2) / 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ (continuous_arctan.intervalIntegrable a b)
  intro x _
  convert ((hasDerivAt_id' x).fun_mul (hasDerivAt_arctan' x)).fun_sub
    ((((hasDerivAt_pow 2 x).const_add 1).log (by positivity)).div_const 2) using 1
  ring

theorem Zad1b_bounds : arctan x ≤ π / 4 ↔ x ≤ 1 := arctan_one ▸ arctan_le_arctan_iff

theorem Zad1b : volume (regionBetween arctan (fun _ => π / 4) (Set.Icc 0 1)) = .ofReal (log 2 / 2) := calc
  volume (regionBetween arctan (fun x => π / 4) (Set.Icc 0 1))
  _ = .ofReal (∫ x in Set.Icc 0 1, π / 4 - arctan x) :=
    volume_regionBetween_eq_integral continuous_arctan.integrableOn_Icc (integrableOn_const (by simp))
      measurableSet_Icc (by simp [Zad1b_bounds])
  _ = .ofReal (∫ x in 0..1, π / 4 - arctan x) := by
    rw [intervalIntegral.integral_of_le (by simp), integral_Icc_eq_integral_Ioc]
  _ = .ofReal (log 2 / 2) := by norm_num [continuous_arctan.intervalIntegrable]
