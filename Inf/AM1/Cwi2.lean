import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.ConditionallyCompleteLattice.Group

namespace AM1.Cwi2

alias Zad1_add := abs_add_le

alias Zad1_sub := abs_abs_sub_abs_le

theorem Zad2a : ∀ n ≥ 3, 2 * n + 1 ≤ 2 ^ n := by
  intro n hn
  induction hn
  case refl => simp
  case step n hn ih => lia

theorem Zad2b : ∀ n : ℕ, 7 ∣ (10 ^ (3 * n + 1) - 3 * (-1) ^ n) := by
  intro n
  induction n
  case zero => simp
  case succ n ih => lia

open Finset in
theorem Zad3_neg (hn : n > 1) (x : ℕ → ℝ) (hx : ∀ i < n, x i ∈ Set.Ioo (-1) 0) :
      1 + ∑ i ∈ range n, x i < ∏ i ∈ range n, (1 + x i) := by
  induction hn
  case refl =>
    simp [range] at *
    ring_nf; simp
    exact mul_pos_of_neg_of_neg (hx 1 le_rfl).right (hx 0 zero_le_one).right
  case step n hn ih =>
    simp [sum_range_succ, prod_range_succ, -Order.lt_add_one_iff] at *
    have ih := ih (Nat.forall_lt_succ_right.mp hx).left
    rw [← add_assoc, mul_add, mul_one]
    apply add_lt_add ih
    have h := prod_lt_prod
      (fun i hi => add_neg_cancel (1 : ℝ) ▸
        add_lt_add_right (hx i (Nat.lt_succ_of_lt <| mem_range.mp hi)).left 1)
      (fun i hi => (add_lt_add_right (hx i (Nat.lt_succ_of_lt <| mem_range.mp hi)).right 1).le)
      ⟨0, by simp; omega, by simpa using (hx 0 n.succ_pos).right⟩
    rw [add_zero, prod_const_one] at h
    exact lt_mul_of_lt_one_left (hx n n.lt_succ_self).right h

open Finset in
theorem Zad3_pos (hn : n > 1) (x : ℕ → ℝ) (hx : ∀ i < n, 0 < x i) :
        1 + ∑ i ∈ range n, x i < ∏ i ∈ range n, (1 + x i) := by
  induction hn
  case refl =>
    simp [range]
    ring_nf; simp
    exact mul_pos (hx 1 one_lt_two) (hx 0 two_pos)
  case step n hn ih =>
    simp [sum_range_succ, prod_range_succ, -Order.lt_add_one_iff] at *
    have ih := ih <| (Nat.forall_lt_succ_right.mp hx).left
    rw [← add_assoc, mul_add, mul_one]
    apply add_lt_add ih
    have h := prod_lt_prod
      (fun i hi => (by simp))
      (fun i hi => (add_lt_add_right (hx i (Nat.lt_succ_of_lt <| Finset.mem_range.mp hi)) 1).le)
      ⟨0, by simp; omega, by simpa using (hx 0 n.succ_pos)⟩
    rw [add_zero, Finset.prod_const_one] at h
    exact lt_mul_of_one_lt_left (hx n n.lt_succ_self) h

theorem Zad3_bernoulli (n : ℕ) (x : ℝ) (hx : -1 < x) : 1 + n * x ≤ (1 + x) ^ n := by
  by_cases! hn : n > 1
  · rcases lt_trichotomy x 0 with h | h | h
    · convert (Zad3_neg hn (fun _ => x) fun _ _ => Set.mem_Ioo.mpr ⟨hx, h⟩).le <;> simp
    · subst h; simp
    · convert (Zad3_pos hn (fun _ => x) fun _ _ => h).le <;> simp
  · cases n
    case neg.zero => simp
    case neg.succ n => simp at hn; subst hn; simp

theorem Zad4 [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ k ≤ n, n.choose k * a ^ (n - k) * b ^ k := by
  rw [add_comm, add_pow, Nat.range_succ_eq_Iic]; ring_nf

theorem Zad5a_inf : sInf { 4 + 1 / (n : ℝ) | n : PNat } = 4 := by
  refine ge_antisymm (le_csInf ?nonempty ?bound) (Real.sInf_le_iff ?bdd ?nonempty |>.mpr ?kres)
  · exists 5, 1; norm_num
  · rintro b ⟨n, hb⟩; subst hb; simp
  · simp [bddBelow_def]
    exists 4; simp
  · intro e he
    exists 4 + 1 / (⌊e⁻¹⌋ + 1); simp
    have hf := Int.floor_nonneg.mpr (inv_pos.mpr he).le
    constructor
    · exists (⌊e⁻¹⌋ + 1).toNat.toPNat (by omega)
      simp [Nat.toPNat]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg]; simp
      omega
    · rw [inv_lt_comm₀]; simp
      · rw [← Int.cast_zero, ← Int.cast_one, ← Int.cast_add, Int.cast_lt]
        omega
      · assumption

theorem Zad5a_sup : sSup { 4 + 1 / (n : ℝ) | n : PNat } = 5 := by
  refine le_antisymm (csSup_le ?nonempty ?bound) (Real.le_sSup_iff ?bdd ?nonempty |>.mpr ?kres)
  · exists 5, 1; norm_num
  · rintro b ⟨n, hb⟩; subst hb; simp
    have h := Nat.cast_inv_le_one (α := ℝ) n; grind
  · simp [bddAbove_def]
    exists 5; intro n;
    have h := Nat.cast_inv_le_one (α := ℝ) n; grind
  · intro e he
    exists 5; simp [he]
    exists 1; simp; norm_num

theorem Zad5b_inf : sInf {x / (x ^ 2 + 1) | (x : Real) (_ : x > 0)} = 0 := by
  refine ge_antisymm (le_csInf ?nonempty ?bound) (Real.sInf_le_iff ?bdd ?nonempty |>.mpr ?kres)
  · exists 1 / 2, 1, (by norm_num); norm_num
  · rintro b ⟨x, hx, hb⟩; subst hb; field_simp; simp; exact hx.le
  · simp [bddBelow_def]
    exists 0; intro x hx; field_simp; simp; exact hx.le
  · intro e he; simp
    exists 1 / e; simp [he]
    rw [div_lt_comm₀]; field_simp; simp; exact sq_pos_of_pos he
    · field_simp; simp; positivity
    · assumption

theorem Zad5b_sup : sSup {x / (x ^ 2 + 1) | (x : Real) (_ : x > 0)} = 1 / 2 := by
  refine le_antisymm (csSup_le ?nonempty ?bound) (Real.le_sSup_iff ?bdd ?nonempty |>.mpr ?kres)
  · exists 1 / 2, 1, (by norm_num); norm_num
  · rintro b ⟨x, hx, hb⟩; subst hb; field_simp
    convert two_mul_le_add_sq x 1 using 1 <;> field
  · simp [bddAbove_def]
    exists 1 / 2; intro x hx; field_simp
    convert two_mul_le_add_sq x 1 using 1 <;> field
  · intro e he; simp
    exists 1; grind

alias Zad6_add := csSup_add

alias Zad6_union := csSup_union

alias Zad7 := csInf_neg

alias Zad8a := ciSup_add_le_ciSup_add_ciSup
