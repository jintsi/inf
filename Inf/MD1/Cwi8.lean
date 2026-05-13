import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.NumberTheory.Real.GoldenRatio

namespace PowerSeries

section variable (R) [Semiring R]

/-- The power series `(1 - X ^ d) / (1 - X)` = `1 + X + ... + X ^ (d - 1)`. -/
def geomSum (d : ℕ) : R⟦X⟧ := mk fun n => if n < d then 1 else 0

theorem coeff_geomSum (d n : ℕ) :
    coeff n (geomSum R d) = if n < d then 1 else 0 := by simp [geomSum]

theorem coeff_geomSum_succ (d n : ℕ) :
    coeff n (geomSum R (d + 1)) = if n ≤ d then 1 else 0 := by simp [geomSum]

end

variable [Ring R] in
theorem geomSum_eq_mk_one_mul : geomSum R d = mk 1 * (1 - X ^ d) := by
  ext n; simp [geomSum, mul_one_sub, coeff_mul_X_pow']; grind

variable [CommRing R] in
@[simp]
theorem geomSum_mul_one_sub : geomSum R d * (1 - X) = 1 - X ^ d := by
  rw [geomSum_eq_mk_one_mul, mul_right_comm, mk_one_mul_one_sub_eq_one, one_mul]

theorem coeff_mul_X' [Semiring R] (φ : R⟦X⟧) (n : ℕ) :
    coeff n (φ * X) = if n = 0 then 0 else coeff (n - 1) φ := by cases n <;> simp

theorem coeff_X_mul' [Semiring R] (φ : R⟦X⟧) (n : ℕ) :
    coeff n (X * φ) = if n = 0 then 0 else coeff (n - 1) φ := by cases n <;> simp

variable [CommSemiring R] in
theorem coeff_prod_fin (f : Fin k → R⟦X⟧) (n : ℕ) :
    coeff n (∏ i, f i) = ∑ l ∈ Finset.finAntidiagonal k n, ∏ i, (f i).coeff (l i) := by
  rw [coeff_prod]; apply Finset.sum_equiv Finsupp.equivFunOnFinite <;> simp

end PowerSeries

namespace MD1.Cwi8

open PowerSeries
open Finset hiding mk

/-- Number of ways to select 70 balls out of 30 red, 40 blue and 50 white ones, computed as
`coeff 70 (geomSum ℤ 31 * geomSum ℤ 41 * geomSum ℤ 51)`. -/
theorem Zad1 : #{rbw ∈ finAntidiagonal 3 70 | rbw 0 ≤ 30 ∧ rbw 1 ≤ 40 ∧ rbw 2 ≤ 50} = 1061 := by
  rw [← Int.natCast_inj]
  calc (#{rbw ∈ finAntidiagonal 3 70 | rbw 0 ≤ 30 ∧ rbw 1 ≤ 40 ∧ rbw 2 ≤ 50} : ℤ)
  _ = ∑ rbw ∈ finAntidiagonal 3 70, coeff (rbw 0) (geomSum ℤ 31) * coeff (rbw 1) (geomSum ℤ 41)
      * coeff (rbw 2) (geomSum ℤ 51) := by
    simp_rw [card_filter, coeff_geomSum]; push_cast; grind
  _ = coeff 70 (∏ i, ![geomSum ℤ 31, geomSum ℤ 41, geomSum ℤ 51] i) := by
    rw [coeff_prod_fin]; simp [Fin.prod_univ_three]
  _ = coeff 70 (mk 1 ^ 3 * (1 - X ^ 31) * (1 - X ^ 41) * (1 - X ^ 51)) := by
    simp [Fin.prod_univ_three, geomSum_eq_mk_one_mul]; ring_nf
  _ = 1061 := by
    ring_nf; simp [coeff_mul_X_pow']; rw [show 3 = 2 + 1 by simp, mk_one_pow_eq_mk_choose_add ℤ 2]
    norm_num [Nat.choose_two_right]

/-- `rescale 2 (invOneSubPow R 2).val` is the multiplicative inverse of `(1 - C 2 * X) ^ 2`. -/
theorem Zad2a_def [CommRing R] : (rescale 2 (invOneSubPow R 2).val) * (1 - C 2 * X) ^ 2 = 1 := by
  rw [show 1 - C 2 * X = rescale 2 (1 - X : R⟦X⟧) by simp, ← map_pow, ← map_mul,
    ← invOneSubPow_inv_eq_one_sub_pow]; simp

theorem Zad2a_coeff [CommRing R] : coeff 5 (rescale 2 (invOneSubPow R 2).val) = 192 := by
  norm_num [invOneSubPow]

/-- `binomialSeries K 3⁻¹` is the cube root of `1 + X`. -/
theorem Zad2b_def [Field K] [CharZero K] : binomialSeries K (3⁻¹ : K) ^ 3 = 1 + X := by
  norm_num [pow_succ, ← binomialSeries_add]; convert binomialSeries_nat 1 <;> simp

theorem Zad2b_coeff [Field K] [CharZero K] : coeff 4 (binomialSeries K (3⁻¹ : K)) = -(10 / 243) := by
  norm_num [Ring.choose_eq_smul, Nat.factorial_succ, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_succ_eval]

theorem Zad2c_def : ((2 * √2) • rescale 2⁻¹ (binomialSeries ℝ (3 / 2 : ℝ)) * mk 1 * (1 - X)) ^ 2 =
    (C 2 + X) ^ 3 := by
  norm_num [mul_assoc, mk_one_mul_one_sub_eq_one, smul_pow, mul_pow, ← map_pow]
  simp [sq, ← binomialSeries_add]; rw [← Nat.cast_three]; simp [-Nat.cast_ofNat, smul_eq_C_mul,
    show C 8 = (C 2 : ℝ⟦X⟧) ^ 3 by norm_num [← map_pow], ← mul_pow, mul_add, ← mul_assoc, ← map_mul]

theorem Zad2c_coeff : coeff 3 ((2 * √2) • rescale 2⁻¹ (binomialSeries ℝ (3 / 2 : ℝ)) * mk 1)
    = 235 / 64 * √2 := by
  norm_num [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, Ring.choose_eq_smul,
    Nat.factorial_succ, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_succ_eval, mul_right_comm]

/-- -6 * X ^ 4 + 6 * X ^ 5 - 6 * X ^ 6 + ... = -6 * X ^ 4 / (1 + X). -/
theorem Zad3a [Ring R] : (mk fun n => if n < 4 then 0 else (-1) ^ (n + 1) * 6 : R⟦X⟧) * (1 + X) = -C 6 * X ^ 4 := by
  ext n
  simp [-eq_intCast, mul_one_add, coeff_X_pow, coeff_mul_X']
  repeat' split
  all_goals simp_all [Nat.sub_one_add_one]
  · lia
  · norm_num
  · lia
  · rw [← add_mul, pow_succ]; simp

/-- 1 + X ^ 2 + X ^ 4 + ... = 1 / (1 - X ^ 2). -/
theorem Zad3b [Ring R] : (mk fun n => if Even n then 1 else 0 : R⟦X⟧) * (1 - X ^ 2) = 1 := by
  ext n
  simp [mul_one_sub, coeff_mul_X_pow']; grind

theorem Zad3d [Semiring R] (c : ℕ) : (mk fun n => c.choose n : R⟦X⟧) = (1 + X) ^ c := by
  trans ∑ n ∈ range (c + 1), c.choose n • X ^ n
  · ext; simp +contextual [-nsmul_eq_mul, coeff_X_pow, Nat.choose_eq_zero_of_lt]
  · symm; rw [add_comm, Commute.add_pow (commute_X 1).symm]; simp [X_pow_mul]

theorem Zad3e [CommRing R] (c : ℕ) : (mk fun n => (c + n - 1).choose n : R⟦X⟧) = invOneSubPow R c := by
  rcases c with _ | c
  · simp [invOneSubPow_zero]; ext n; cases n <;> simp
  simp [invOneSubPow_val_succ_eq_mk_add_choose, ← Nat.choose_symm_add]

theorem Zad3f [CommRing R] (c : R) : (mk fun n => c ^ n) * (1 - C c * X) = 1 := by
  trans rescale c (mk 1 * (1 - X))
  · simp [rescale_mk]
  · simp [mk_one_mul_one_sub_eq_one]

theorem Zad3g [CommRing R] (m : ℕ) : (mk fun n => (m + n).choose m : R⟦X⟧) = invOneSubPow R (m + 1) := rfl

theorem Zad3h [CommRing A] [Algebra ℚ A] : (mk fun n => algebraMap ℚ A (1 / n)) = -logOf (1 - X) := by
  rw [logOf, sub_sub_cancel_left, ← neg_one_smul A X, ← rescale_eq_subst]
  simp [log, rescale_mk]; ext n
  cases n <;> simp [pow_succ]
  rw [← map_one (algebraMap ℚ A), ← map_neg, ← map_pow, ← map_mul]
  congr; simp [mul_div, ← pow_add]

theorem Zad3i [Ring A] [Algebra ℚ A] : (mk fun n => algebraMap ℚ A (1 / n.factorial)) = exp A := rfl

theorem Zad4a [CommRing R] (g : R⟦X⟧) (n : ℕ) :
    coeff n (g + rescale (-1) g) = if Even n then 2 * coeff n g else 0 := by
  split <;> simp_all [two_mul]

theorem Zad4b [CommRing R] (g : R⟦X⟧) (n : ℕ) :
    coeff n (g - rescale (-1) g) = if Even n then 0 else 2 * coeff n g := by
  split <;> simp_all [two_mul]

theorem Zad5_fun [CommRing R] :
    (mk fun n => #{ijk ∈ finAntidiagonal 3 n | 3 ∣ ijk 1 ∧ ijk 1 ≠ 0 ∧ 3 ∣ ijk 2 ∧ ijk 2 ≠ 0} : R⟦X⟧)
    = mk 1 * (expand 3 (by simp) (mk 1)) ^ 2 * X ^ 6 := calc
  (mk fun n => #{ijk ∈ finAntidiagonal 3 n | 3 ∣ ijk 1 ∧ ijk 1 ≠ 0 ∧ 3 ∣ ijk 2 ∧ ijk 2 ≠ 0} : R⟦X⟧)
  _ = ∏ i, ![mk 1, expand 3 (by simp) (mk 1) * X ^ 3, expand 3 (by simp) (mk 1) * X ^ 3] i := by
    ext n; simp [coeff_prod_fin]; rw [card_filter]; push_cast; congr; funext ijk
    simp [Fin.prod_univ_three, coeff_mul_X_pow', coeff_expand]; grind
  _ = mk 1 * (expand 3 (by simp) (mk 1)) ^ 2 * X ^ 6 := by simp [Fin.prod_univ_three]; ring

theorem Zad6a (r : ℕ) : (mk fun n => #(finAntidiagonal r n)) = mk 1 ^ r := by
  ext n; simp [← Fin.prod_const, -prod_const, coeff_prod_fin]

theorem Zad6b (r n : ℕ) : #(finAntidiagonal (r + 1) n) = (r + n).choose r := by zify; calc
  (#(finAntidiagonal (r + 1) n) : ℤ) = coeff n (mk fun n => #(finAntidiagonal (r + 1) n)) := by simp
  _ = (coeff n) (mk 1 ^ (r + 1)) := by rw [Zad6a, ← Nat.coe_castRingHom, ← coeff_map, map_pow]; rfl
  _ = (r + n).choose r := by simp [mk_one_pow_eq_mk_choose_add]

theorem Zad7 [Semiring R] (a : R⟦X⟧) : a * mk 1 = mk fun n => ∑ i ∈ range (n + 1), coeff i a := by
  ext n; simp [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem Zad7a : (∑ i ∈ range (n + 1), i ^ 2 : ℚ) = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n
  · simp
  rename_i n ih
  rw [sum_range_succ, ih]; push_cast; ring

theorem Zad7b : (∑ i ∈ range (n + 1), i ^ 3 : ℚ) = n ^ 2 * (n + 1) ^ 2 / 4 := by
  induction n
  · simp
  rename_i n ih
  rw [sum_range_succ, ih]; push_cast; ring

namespace Zad8

/-- `A 0 = 2, A 1 = 3, A (n + 2) = 3 * A n - 2 * A (n + 1)` -/
def A : ℕ → ℤ
  | 0     => 2
  | 1     => 3
  | n + 2 => 3 * A n - 2 * A (n + 1)

theorem A_eq : (A n : ℚ) = (9 - (-3) ^ n) / 4 := by
  induction n using Nat.twoStepInduction
  case zero => norm_num [A]
  case one  => norm_num [A]
  case more n ih₀ ih₁ => simp_all [A]; ring

/-- `B 0 = 0, B 1 = 1, B (n + 2) = 4 * B (n + 1) - 4 * B n` -/
def B : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => 4 * B (n + 1) - 4 * B n

theorem B_eq : B n = n * 2 ^ (n - 1) := by
  induction n using Nat.twoStepInduction
  case zero => rfl
  case one  => rfl
  case more n ih₀ ih₁ => simp_all [B]; cases n <;> simp; ring_nf; omega

/-- `C 0 = 1, C (n + 1) = 2 * C n + 3` -/
def C : ℕ → ℕ
  | 0     => 1
  | n + 1 => 2 * C n + 3

theorem C_eq : C n = 2 ^ (n + 2) - 3 := by
  rw [eq_tsub_iff_add_eq_of_le (by grw [← n.zero_le] <;> simp)]
  induction n
  case zero => rfl
  case succ n ih => rw [C, add_assoc, ← two_mul, ← mul_add, ih, mul_comm]; rfl

end Zad8

namespace Zad9

/-- `A 0 = A 1 = 4, A (n + 2) = A (n + 1) + 6 * A n` -/
def A : ℕ → ℕ
  | 0     => 4
  | 1     => 4
  | n + 2 => A (n + 1) + 6 * A n

theorem A_eq : (A n : ℚ) = 4 / 5 * (3 ^ (n + 1) - (-2) ^ (n + 1)) := by
  induction n using Nat.twoStepInduction
  case zero => norm_num [A]
  case one  => norm_num [A]
  case more n ih₀ ih₁ => simp_all [A]; ring

/-- `B 0 = B 1 = 2, B (n + 2) = 2 * B (n + 1) - B n` -/
def B : ℕ → ℕ
  | 0     => 2
  | 1     => 2
  | n + 2 => 2 * B (n + 1) - B n

theorem B_eq : B n = 2 := by
  induction n using Nat.twoStepInduction
  case zero => rfl
  case one  => rfl
  case more n ih₀ ih₁ => simp_all [B]

/-- `C 0 = 0, C 1 = 1, C (n + 2) = C (n + 1) + C n + 1` -/
def C : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => C (n + 1) + C n + 1

theorem C_eq_fib : C n = Nat.fib (n + 2) - 1 := by
  rw [eq_tsub_iff_add_eq_of_le (by rw [← Nat.fib_two]; apply Nat.fib_mono; simp)]
  induction n using Nat.twoStepInduction
  case zero => rfl
  case one  => rfl
  case more n ih₀ ih₁ => rw [Nat.fib_add_two, C, add_assoc, add_add_add_comm, ih₀, ih₁, add_comm]

theorem C_eq : (C n : ℝ) = (Real.goldenRatio ^ (n + 2) - Real.goldenConj ^ (n + 2)) / √5 - 1 := by
  rw [C_eq_fib, Nat.cast_sub, Nat.cast_one, Real.coe_fib_eq]
  rw [← Nat.fib_two]; apply Nat.fib_mono; simp

/-- `D 0 = 0, D 1 = 1, D (n + 2) = 2 * D (n + 1) - D n` -/
def D : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => 2 * D (n + 1) - D n

theorem D_eq : D n = n := by
  induction n using Nat.twoStepInduction
  case zero => rfl
  case one  => rfl
  case more n ih₀ ih₁ => simp_all [D]; omega

/-- `E 0 = 0, E 1 = 1, E (n + 2) = E (n + 1) - E n` -/
def E : ℕ → ℤ
  | 0     => 0
  | 1     => 1
  | n + 2 => E (n + 1) - E n

theorem E_eq : E n = ![0, 1, 1, 0, -1, -1] (Fin.ofNat 6 n) := by
  induction n using Nat.twoStepInduction
  case zero => rfl
  case one  => rfl
  case more n ih₀ ih₁ =>
    simp_all [E, -Fin.ofNat_eq_cast]
    convert_to ![0, 1, 1, 0, -1, -1] (Fin.ofNat 6 n + 1)
      - ![0, 1, 1, 0, -1, -1] (Fin.ofNat 6 n)
      = ![0, 1, 1, 0, -1, -1] (Fin.ofNat 6 n + 2)
    · rw [Fin.ofNat_add]; simp
    · rw [Fin.ofNat_add]; simp
    generalize Fin.ofNat 6 n = i
    fin_cases i <;> simp

/-- `F 0 = 1, F 1 = 5, F 2 = 11, F (n + 3) = 3 * F (n + 2) + 2 * F (n + 1) - 2 * F n` -/
def F : ℕ → ℤ
  | 0     => 1
  | 1     => 5
  | 2     => 11
  | n + 3 => 3 * F (n + 2) + 2 * F (n + 1) - 2 * F n

theorem F_eq : F n = (2 - √2) ^ n + (2 + √2) ^ n - (-1) ^ n := by
  induction n using Nat.stepInduction 3
  case base n hn =>
    revert n
    norm_num [Nat.forall_lt_succ_right, -Order.lt_two_iff, sub_sq, add_sq, F]; ring
  case step n ih =>
    obtain ⟨⟨ih₀, ih₁⟩, ih₂⟩ := by simpa [Nat.forall_lt_succ_right, -Order.lt_two_iff] using ih
    simp_all [F, pow_succ]; ring_nf; simp [pow_three]; ring

/-- `G 0 = G 1 = 1, G (n + 2) = G (n + 1) + 2 * G n + (-1) ^ n` -/
def G : ℕ → ℤ
  | 0     => 1
  | 1     => 1
  | n + 2 => G (n + 1) + 2 * G n + (-1) ^ n

theorem G_eq : (G n : ℚ) = (7 * 2 ^ n + (3 * n + 2) * (-1) ^ n) / 9 := by
  induction n using Nat.twoStepInduction
  case zero => norm_num [G]
  case one  => norm_num [G]
  case more n ih₀ ih₁ => simp_all [G]; ring

/-- `H 0 = H 1 = 1, H (n + 2) = H (n + 1) + 6 * H n - n` -/
def H : ℕ → ℤ
  | 0     => 1
  | 1     => 1
  | n + 2 => H (n + 1) + 6 * H n - n

theorem H_eq : (H n : ℚ) = 11 / 20 * 3 ^ n + 19 / 45 * (-2) ^ n + n / 6 + 1 / 36 := by
  induction n using Nat.twoStepInduction
  case zero => norm_num [H]
  case one  => norm_num [H]
  case more n ih₀ ih₁ => simp_all [H]; ring

/-- `I 0 = 1, I (n + 1) = 2 * I n + 4 ^ n` -/
def I : ℕ → ℕ
  | 0     => 1
  | n + 1 => 2 * I n + 4 ^ n

theorem I_eq : 2 * I n = 2 ^ n + 4 ^ n := by
  induction n
  case zero => rfl
  case succ n ih => rw [I, ih]; ring

end Zad9
