import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace MD1.Cwi4

theorem Zad1 (n : ℕ) : n.stirlingSecond 2 = 2 ^ (n - 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Nat.stirlingSecond_succ_succ, ih, Nat.mul_sub, ← pow_succ']
      cases n <;> simp [Nat.stirlingSecond_one_right]; grind

/-- `Equiv.Perm.cycleType` doesn't include ones, so here `λ₁ = card α - m.sum`,
  otherwise `λi = m.count i` -/
theorem Zad2 [Fintype α] [DecidableEq α] (m : Multiset ℕ) (hm : ∀ i ∈ m, 2 ≤ i)
    (hα : m.sum ≤ Fintype.card α) : Finset.card {g : Equiv.Perm α | g.cycleType = m} =
    (Fintype.card α).factorial / (m.prod * (Fintype.card α - m.sum).factorial *
      ∏ i ∈ m.toFinset, (m.count i).factorial) := by
  rw [Equiv.Perm.card_of_cycleType]; simp_all [mul_comm]

theorem Zad3 [DecidableEq α] [CommSemiring R] (s : Finset α) (x : α → R) (N : ℕ) :
    (∑ i ∈ s, x i) ^ N = ∑ n ∈ s.piAntidiag N,
      (N.factorial / ∏ i ∈ s, (n i).factorial) • ∏ i ∈ s, x i ^ n i := by
  simp [Finset.sum_pow_eq_sum_piAntidiag, Nat.multinomial]; congr!; simp_all

theorem _root_.Nat.sum_range_stirlingFirst (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), n.stirlingFirst i = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.sum_range_succ' _ (n + 1), Nat.stirlingFirst_succ_zero, add_zero,
      Nat.stirlingFirst_succ_succ, Finset.sum_add_distrib, Nat.factorial_succ, ← ih, add_one_mul,
      Finset.mul_sum]
    congr 1; rw [Finset.sum_range_succ, Finset.sum_range_succ']
    cases n <;> simp [Nat.stirlingFirst_eq_zero_of_lt]

theorem Zad4 (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i * n.stirlingFirst i =
    n.factorial * harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, mul_add, Nat.factorial_succ, Nat.cast_mul,
      mul_right_comm _ _ _⁻¹, mul_inv_cancel₀ (by positivity), one_mul, mul_assoc, ← ih]
    norm_cast
    calc ∑ i ∈ Finset.range (n + 2), i * (n + 1).stirlingFirst i
    _ = ∑ i ∈ Finset.range (n + 1), (i + 1) * (n * n.stirlingFirst (i + 1) + n.stirlingFirst i) := by
      rw [Finset.sum_range_succ']; rfl
    _ = n * ∑ i ∈ Finset.range (n + 1), (i + 1) * n.stirlingFirst (i + 1) +
        ∑ i ∈ Finset.range (n + 1), i * n.stirlingFirst i +
        ∑ i ∈ Finset.range (n + 1), n.stirlingFirst i := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm, Finset.mul_sum, add_assoc]
      congr; simp_rw [add_one_mul, Finset.sum_add_distrib]
    _ = (n + 1) * ∑ i ∈ Finset.range (n + 1), i * n.stirlingFirst i + n.factorial := by
      rw [add_one_mul, Nat.sum_range_stirlingFirst]; congr 3
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp [Nat.stirlingFirst_eq_zero_of_lt]


open Polynomial

theorem Zad5a [Ring R] (n : ℕ) : X ^ n =
    ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k • descPochhammer R k := by
  induction n with
  | zero => simp
  | succ n ih => calc
    X ^ (n + 1) = X ^ n * X := pow_succ X n
    _ = ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k • descPochhammer R k * (↑k + (X - ↑k)) := by
      simp_rw [ih, Finset.sum_mul, add_sub_cancel]
    _ = ∑ k ∈ Finset.range (n + 1), (k * n.stirlingSecond k) • descPochhammer R k +
        ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k • descPochhammer R k * (X - ↑k) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← nsmul_eq_mul', smul_smul]
    _ = _ + ∑ k ∈ Finset.range (n + 1), n.stirlingSecond k • descPochhammer R (k + 1) := by
      congr! 2 with k hk; rw [descPochhammer_succ_right, smul_mul_assoc]
    _ = _ + ∑ k ∈ Finset.Ico 1 (n + 2), n.stirlingSecond (k - 1) • descPochhammer R k := by
      rw [← Finset.sum_Ico_add' _ 0 (n + 1) 1]; congr; simp
    _ = ∑ k ∈ Finset.range (n + 2), (n + 1).stirlingSecond k • descPochhammer R k := by
      rw [Finset.sum_range_eq_add_Ico, Finset.sum_range_eq_add_Ico, add_assoc] <;> try positivity
      congr 1; · simp
      rw [Finset.sum_Ico_succ_top le_add_self, Finset.sum_Ico_succ_top le_add_self, ← add_assoc]
      congr 2; swap; · simp [Nat.stirlingSecond_self]
      rw [← Finset.sum_add_distrib]; congr! 1 with k hk
      rw [Nat.stirlingSecond_succ_left, add_smul]
      grind

theorem Zad5b [Semiring S] (n : ℕ) : ascPochhammer S n =
    ∑ k ∈ Finset.range (n + 1), n.stirlingFirst k • X ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [ascPochhammer_succ_right, add_comm X, ih, Finset.sum_mul, mul_add,
      Finset.sum_add_distrib, ← nsmul_eq_mul', smul_smul, smul_mul_assoc, ← pow_succ,
      Finset.sum_range_succ' _ (n + 1), Nat.stirlingFirst_succ_zero, zero_nsmul, add_zero,
      Nat.stirlingFirst_succ_succ, add_smul, Finset.sum_add_distrib]
    congr 1; rw [Finset.sum_range_succ', Finset.sum_range_succ]; congr 1
    cases n <;> simp [Nat.stirlingFirst_eq_zero_of_lt]
