import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.PrimeFin

namespace Elitm.Cwi0

open Finset

theorem Zad1 : ∑ i ∈ range (n + 2), i * 2 ^ i = 2 + n * 2 ^ (n + 2) := by
  induction n with
  | zero => simp [sum_range_succ]
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem Zad2 : ∑ i ∈ range n, ((i + 1) * (i + 2) : ℚ)⁻¹ = n / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; field_simp; norm_cast; ring

theorem Zad3 : (∑ i ∈ range (n + 1), i ^ 2) * 6 = 2 * n ^ 3 + 3 * n ^ 2 + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; ring

theorem Zad4 : (∑ i ∈ range (n + 1), i ^ 3) * 4 = n ^ 2 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; ring

theorem Zad5 : (∑ i ∈ range (n + 1), i * (i + 1)) * 3 = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; ring

theorem Zad6 : ∑ i ∈ range (n + 1), (2 * i) ^ 3 = 2 * n ^ 2 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem Zad7 : ∑ i ∈ range n, i * i.factorial = n.factorial - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, ← Nat.sub_add_comm n.factorial_pos, Nat.factorial_succ]; ring_nf

open Real in
theorem Zad8 {n : ℕ} (h : 2 ≤ n) : √n < ∑ i ∈ range n, (√(i + 1))⁻¹ := by
  induction n, h using Nat.le_induction with
  | base => norm_num [sum_range_succ, ← sqrt_div_self]; field_simp; simp [mul_two]
  | succ n h ih =>
    grw [sum_range_succ, ← ih]; field_simp; norm_cast
    rw [mul_self_sqrt (by positivity), Nat.cast_add_one, add_le_add_iff_right]
    nth_rw 1 [← mul_self_sqrt (x := n) (by positivity)]; apply mul_le_mul_of_nonneg_left
    · apply Real.sqrt_le_sqrt; simp
    · simp

theorem Zad9 : n ^ 3 < 4 ^ n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
  rcases this with rfl | rfl | rfl | h <;> simp
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    grw [pow_succ 4, ← ih]; ring_nf; simp only [(show 4 = 1 + 1 + 1 + 1 by rfl), mul_add, mul_one]
    gcongr
    · grw [← h]; simp
    · grw [h, ← sq]; apply Nat.pow_le_pow_right; positivity; simp
    · grw [h]; rfl

theorem Zad10 : 2 * n ^ 2 < 3 ^ n := by
  have : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
  rcases this with rfl | rfl | h <;> simp
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    grw [pow_succ 3, ← ih, add_sq, show 3 = 1 + 1 + 1 by rfl]
    simp [-Nat.reduceAdd, mul_add]; gcongr
    · grw [h, sq]
    · grw [← h]; simp

theorem Zad11 (h : 6 ≤ n) : 5 * n ≤ n ^ 2 - 3 := by
  induction n, h using Nat.le_induction with grind

theorem Zad12 (h : 0 < n) : 8 ∣ 5 ^ n + 2 * 3 ^ (n - 1) + 1 := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    convert_to 8 ∣ 5 * (5 ^ n + 2 * 3 ^ (n - 1) + 1) - 4 * (3 ^ (n - 1) + 1)
    · rw [n.sub_add_comm h]; grind
    apply Nat.dvd_sub (ih.mul_left 5); apply mul_dvd_mul_left 4 (b := 2)
    rw [← even_iff_two_dvd, Nat.even_add_one, Nat.not_even_iff_odd]
    apply Odd.pow; use 1; rfl

theorem Zad13 : 8 ∣ 11 ^ n - 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    convert (dvd_mul_right 8 (11 ^ n)).add (ih.mul_left 3); rfl
    rw [Nat.mul_sub, ← Nat.add_sub_assoc (by gcongr; simp)]; ring_nf

theorem Zad14 : 11 ∣ 2 ^ (6 * n + 1) + 3 ^ (2 * n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    convert (dvd_mul_right 11 (5 * 2 ^ (6 * n + 1))).add (ih.mul_left 9) using 1; rfl; ring

theorem Zad15 : 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
  convert (ih.mul_left 11).add (dvd_mul_right 133 (12 ^ (2 * n + 1))) using 1; rfl
  ring

theorem Zad16 : 9 ∣ 4 ^ n + 24 * n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    convert Nat.dvd_sub ((ih.mul_left 4).add (dvd_mul_right 9 3)) (dvd_mul_right 9 (8 * n)) using 1
    grind

theorem Zad19 [DivisionSemiring R] {a : ℕ → R} (h : ∀ n, a (n + 1) = a n / (2 * a n + 1))
    (hne : ∀ n, a n ≠ 0) (n : ℕ) : a n = (2 * n + (a 0)⁻¹)⁻¹ := by
  rw [← inv_eq_iff_eq_inv]; induction n with
  | zero => simp
  | succ n ih => rw [h, inv_div, add_div, mul_div_cancel_right₀ _ (hne n), one_div, ih,
      ← add_assoc, add_comm 2, Nat.cast_add_one, mul_add_one]

alias Zad23 := Nat.infinite_setOf_prime
alias Zad24 := Nat.primeFactorsList_unique
