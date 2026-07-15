import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Factorization.Basic

namespace Elitm.Cwi6

open Set

theorem Zad2a_image : (fun x : ℝ => x ^ 2) '' Ico (-2) 3 = Ico 0 9 := by
  rw [← Icc_union_Ico_eq_Ico (b := 0) (by simp) (by simp), image_union,
    ContinuousOn.image_Icc_of_antitoneOn (by simp) (by fun_prop),
    ContinuousOn.image_Ico_of_strictMonoOn (by simp) (by fun_prop)]
  · norm_num [Set.Icc_subset_Ico_right]
  · intro x ⟨hx, _⟩ y _ h; apply pow_lt_pow_left₀ h hx; trivial
  · intro x ⟨_, hx⟩ y ⟨_, hy⟩ h; rwa [sq_le_sq, abs_of_nonpos hx, abs_of_nonpos hy, neg_le_neg_iff]

theorem Zad2a_preimage : (fun x : ℝ => x ^ 2) ⁻¹' Ico 0 9 = Ioo (-3) 3 := by
  ext x; simp [sq_nonneg, Real.sq_lt, show √9 = 3 by norm_num [Real.sqrt_eq_iff_eq_sq]]

theorem Zad2b_image [AddZeroClass M] [One M] :
    (fun p : M × M => p.1 + p.2) '' {(0, 0), (0, 1)} = {0, 1} := by simp [image_pair]

theorem Zad2b_preimage [Add M] [Zero M] [One M] :
    (fun p : M × M => p.1 + p.2) ⁻¹' {0, 1} = {(x, y) | x + y = 0} ∪ {(x, y) | x + y = 1} := rfl

theorem Zad2c_image : (fun p : ℕ × ℕ => p.1 / (p.2 + 1 : ℚ)) '' {(1, 2)} = {1 / 3} := by norm_num

theorem Zad2c_preimage :
    (fun p : ℕ × ℕ => p.1 / (p.2 + 1 : ℚ)) ⁻¹' {1 / 3} = {(x, y) | 3 * x = y + 1} := by
  ext; simp; field_simp; norm_cast; rw [mul_comm]

open Polynomial in
theorem Zad2d_image [Ring R] : eval (1 : R) '' {p | ∃ a : R, p = C a * X - C a} = {0} := by
  ext x; simpa using eq_comm

open Polynomial in
theorem Zad2d_preimage [CommRing R] : eval (1 : R) ⁻¹' {0} = {p | X - 1 ∣ p} := by
  ext p; simp [← IsRoot.def, ← dvd_iff_isRoot]

theorem Zad2e_image [Ring R] [Invertible (2 : R)] :
    (fun p : R × R => (p.1 + p.2, p.1 - p.2)) '' Set.diagonal R = Set.univ ×ˢ {0} := by
  ext ⟨x, y⟩; simp [eq_comm]; intro _; use x * ⅟2; rw [← mul_two, invOf_mul_cancel_right]

theorem Zad2e_preimage [NonUnitalNonAssocRing R] :
    (fun p : R × R => (p.1 + p.2, p.1 - p.2)) ⁻¹' Set.univ ×ˢ {0} = Set.diagonal R := by
  ext ⟨x, y⟩; simpa using sub_eq_zero

theorem Zad2f_image :
    (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) '' Set.Ioo 1 2 ×ˢ Set.Ioo 0 1 = Set.Ioo 1 5 := calc
  (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) '' Set.Ioo 1 2 ×ˢ Set.Ioo 0 1
  _ = (fun p => p.1 + p.2) '' ((· ^ 2) '' Set.Ioo 1 2) ×ˢ ((· ^ 2) '' (Set.Ioo 0 1)) := by
    ext r; simp [-image2_add]; tauto
  _ = (fun p => p.1 + p.2) '' Set.Ioo 1 4 ×ˢ Set.Ioo 0 1 := by
    congr; all_goals
    rw [ContinuousOn.image_Ioo_of_strictMonoOn (by simp) (by fun_prop)]; norm_num
    intro x ⟨_, _⟩ y _ h; apply pow_lt_pow_left₀ h (by linarith); trivial
  _ = Set.Ioo 1 5 := by
    ext r; constructor <;> simp [-image2_add]
    · intros; and_intros <;> linarith
    · intro hl hu
      use (3 * r + 1) / 4, (by and_intros <;> linarith), (r - 1) / 4, by and_intros <;> linarith
      field

theorem Zad2g_image :
    (fun p : ℝ × ℝ => max p.1 p.2) '' {(x, y) | x ^ 2 + y ^ 2 = 1} = Set.Icc (-√2 / 2) 1 := by
  ext x; constructor <;> simp
  · rintro x y h rfl; and_intros
    · contrapose! h; simp at h; apply ne_of_gt; grw [← neg_sq, ← neg_sq y, h.1, h.2]
      · norm_num [div_pow]
      · simp [neg_div]; positivity
      · simp [neg_div]; positivity
    · simp; and_intros <;> nlinarith
  · intro hl hu; use x, -√(1 - x ^ 2); and_intros
    · rw [neg_sq, Real.sq_sqrt, add_sub_cancel]; simp [abs_le, hu]
      grw [← hl]; field_simp; simp
    rw [sup_eq_left, neg_le]; by_cases! hu : -x < 0
    · grw [hu]; simp
    apply Real.le_sqrt_of_sq_le; simp [le_sub_iff_add_le]; grw [← two_mul, ← neg_sq, ← hl]
    norm_num [div_pow]

theorem Zad2g_preimage : (fun p : ℝ × ℝ => max p.1 p.2) ⁻¹' Set.Icc (-√2 / 2) 1 =
    Set.Iic 1 ×ˢ Set.Icc (-√2 / 2) 1 ∪ Set.Icc (-√2 / 2) 1 ×ˢ Set.Iic 1 := by
  ext ⟨x, y⟩; simp; tauto

theorem Zad2h_image : (fun n : ℕ => n.primeFactors.sum id) '' {4, 6} = {2, 5} := by
  simp [image_pair, Nat.primeFactors_mul, -Nat.reduceMul, show 4 = 2 * 2 from rfl,
    show 6 = 2 * 3 from rfl, Nat.prime_two, Nat.prime_three]

theorem Zad2h_preimage : (fun n : ℕ => n.primeFactors.sum id) ⁻¹' {2, 5} =
    {n | (∃ k, n = 2 ^ (k + 1)) ∨ (∃ k l, n = 2 ^ (k + 1) * 3 ^ (l + 1)) ∨ ∃ k, n = 5 ^ (k + 1)} := by
  ext n; simp; congr!
  · constructor; swap
    · rintro ⟨k, rfl⟩; simp [Nat.primeFactors_prime_pow _ Nat.prime_two]
    intro h; have : n.primeFactors = {2} := by
      rw [Finset.eq_singleton_iff_nonempty_unique_mem]; and_intros
      · contrapose! h; simp [h]
      intro x hx; apply le_antisymm
      · rw [← h]; apply Finset.single_le_sum_of_canonicallyOrdered hx
      · exact (Nat.prime_of_mem_primeFactors hx).two_le
    rw [← Nat.support_factorization, Finsupp.support_eq_singleton] at this
    use n.factorization 2 - 1; rw [Nat.sub_one_add_one this.1]
    apply Nat.eq_pow_of_factorization_eq_single ?_ this.2; contrapose! h; simp [h]
  · constructor; swap
    · rintro (⟨k, l, rfl⟩ | ⟨k, rfl⟩) <;> simp [Nat.primeFactors_mul, Nat.primeFactors_prime_pow,
        Nat.prime_two, Nat.prime_three, Nat.prime_five]
    intro h; by_cases h2 : 2 ∈ n.primeFactors; map_tacs [left; right]
    · have h' : ∑ x ∈ n.primeFactors.erase 2, x = 3 := by
        zify at ⊢ h; rw [Finset.sum_erase_eq_sub] <;> simp [h, h2]
      have : n.primeFactors = {2, 3} := by
        suffices n.primeFactors.erase 2 = {3} by rw [← Finset.insert_erase h2, this]
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]; and_intros
        · contrapose! h'; simp [h']
        intro x hx; have : x ≠ 2 := Finset.ne_of_mem_erase hx
        have := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx)).two_le
        have := (Finset.single_le_sum_of_canonicallyOrdered hx).trans_eq h'
        omega
      rw [← Nat.support_factorization] at this; use n.factorization 2 - 1, n.factorization 3 - 1
      rw [Nat.sub_one_add_one (by rw [← Finsupp.mem_support_iff, this]; simp),
          Nat.sub_one_add_one (by rw [← Finsupp.mem_support_iff, this]; simp)]
      symm; convert Nat.prod_factorization_pow_eq_self (n := n) (by contrapose h; simp [h])
      rw [Finsupp.prod, this, Finset.prod_pair]; simp
    · have : n.primeFactors = {5} := by
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]; and_intros
        · contrapose! h; simp [h]
        intro x hx; apply le_antisymm
        · rw [← h]; apply Finset.single_le_sum_of_canonicallyOrdered hx
        apply (Nat.prime_of_mem_primeFactors hx).five_le_of_ne_two_of_ne_three
        · contrapose! h2; rwa [← h2]
        contrapose! h2; subst x; rename' hx => h3
        suffices n.primeFactors.erase 3 = {2} by
          simp [Finset.ext_iff, -Nat.mem_primeFactors] at this; exact ((this 2).mpr rfl).2
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]; and_intros
        · contrapose! h; rw [← Finset.insert_erase h3, h]; simp
        intro x hx; apply le_antisymm
        · trans ∑ x ∈ n.primeFactors.erase 3, x
          · apply Finset.single_le_sum_of_canonicallyOrdered hx
          zify at ⊢ h; rw [Finset.sum_erase_eq_sub h3, h]; simp
        · exact (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx)).two_le
      rw [← Nat.support_factorization, Finsupp.support_eq_singleton] at this
      use n.factorization 5 - 1; rw [Nat.sub_one_add_one this.1]
      apply Nat.eq_pow_of_factorization_eq_single ?_ this.2; contrapose! h; simp [h]

theorem Zad2j_image [Nonempty β] :
    (fun s : Set (α × β) => {x | ∃ y, (x, y) ∈ s}) '' {s | ∃ p, s = {p}} = {s | ∃ x, s = {x}} := by
  ext s; simp [eq_comm]

theorem Zad2j_preimage : (fun s : Set (α × β) => {x | ∃ y, (x, y) ∈ s}) ⁻¹' {s | ∃ x, s = {x}} =
    {s | ∃ x ys, ys.Nonempty ∧ s = {x} ×ˢ ys} := by
  ext s; constructor <;> simp
  · intro x hx; use x, {y | (x, y) ∈ s}; and_intros
    · simp [Set.ext_iff] at hx; exact (hx x).mpr rfl
    rw [← hx]; simp [Set.ext_iff] at ⊢ hx; intro a b; constructor
    · intro h; use! b; convert h; symm; rw [← hx]; use b
    · rw [hx]; simp +contextual
  rintro x s ⟨y, hy⟩ rfl; use x; ext a; simp; intro; use y

alias Zad3a := Set.subset_preimage_image
alias Zad3a' := Set.preimage_image_eq
alias Zad3b := Set.image_inter_subset
alias Zad3b' := Set.image_inter
alias Zad3c := Set.image_sdiff_subset
alias Zad3c' := Set.image_sdiff

theorem Zad4 [Finite α] [Nonempty α] (f : α → α) : ∃ s : Set α, s.Nonempty ∧ f '' s = s := by
  have a := Classical.arbitrary α
  have := not_injective_infinite_finite fun n => f^[n] a; simp [Function.Injective] at this
  rcases this with ⟨b, c, h, hne⟩; wlog hb : b < c generalizing b c
  · exact this c b h.symm (Ne.symm hne) (lt_of_ne_of_le' hne (le_of_not_gt hb))
  use (fun n => f^[n] a) '' Set.Ici b; and_intros
  · use f^[b] a, b, le_refl b
  ext x; constructor <;> simp
  · rintro n hn rfl; use n + 1, hn.step; rw [Function.iterate_succ_apply']
  rintro n hn rfl; cases hn with
  | refl => use c - 1, Nat.le_sub_one_of_lt hb; rw [← Function.iterate_succ_apply' f, h,
    Nat.succ_eq_add_one, Nat.sub_one_add_one (Nat.ne_zero_of_lt hb)]
  | @step n hn => use n, hn; rw [Function.iterate_succ_apply']
