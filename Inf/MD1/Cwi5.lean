import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Sym

open Finset

variable [DecidableEq α] [Fintype α]

theorem Finset.inf_filter {s : Finset ι} (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    s.inf (fun i => univ.filter (p i)) = ({a | ∀ i ∈ s, p i a} : Finset _) := by
  ext a; simp [mem_inf]

theorem Finset.inf_univ_filter [Fintype ι] (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    univ.inf (fun i => univ.filter (p i)) = ({a | ∀ i, p i a} : Finset _) := by
  simp [inf_filter]

namespace MD1.Cwi5

/-- The union version is already proven as `Finset.inclusion_exclusion_card_biUnion`,
so here's just the intersection version -/
theorem Zad1_inf (s : Finset ι) (S : ι → Finset α) :
    (s.inf S).card = ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card * (t.inf fun i => (S i)ᶜ).card := by
  simp [← inclusion_exclusion_card_inf_compl]

open Fintype in
theorem Zad2 [DecidableEq β] [Fintype β] : #{f : α → β | f.Surjective} =
    ∑ j ∈ range (card β + 1), (-1 : ℤ) ^ j * (card β).choose j * (card β - j) ^ card α := by
  unfold Function.Surjective
  rw [← inf_univ_filter, Zad1_inf]
  simp_rw [powerset_univ, compl_filter, not_exists, inf_filter]
  calc
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * #{f : α → β | ∀ b ∈ t, ∀ a, ¬f a = b} := by
    congr!
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * card (α → ↥tᶜ) := by
    congr! with t ht; symm; rw [← card_congr Equiv.subtypePiEquivPi]
    apply card_of_subtype; simp; grind only
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * ↑(card β - t.card) ^ card α := by simp
  _ = ∑ j ∈ range (card β + 1), (-1 : ℤ) ^ j * (card β).choose j * (card β - j) ^ card α := by
    rw [← powerset_univ, sum_powerset_apply_card fun j => _ * (_ - j).cast ^ _]
    simp_rw [card_univ, Int.nsmul_eq_mul, ← mul_assoc, mul_comm (Nat.cast _)]
    congr! with j hj; simp_all

alias Zad4 := numDerangements_add_two

theorem Zad5a (h : k ≤ n) : Nat.stirlingSecond n k =
    ∑ s ∈ (range (k + 1)).sym (n - k), s.toMultiset.prod := by
  induction n generalizing k
  · rw [nonpos_iff_eq_zero] at h; subst h; simp [Sym.eq_nil_of_card_zero]
  cases k
  · simp [Sym.coe_cons]
  rename_i n ih k; rw [add_le_add_iff_right] at h; rw [show n + 1 - (k + 1) = n - k by simp]
  rcases h.eq_or_lt with h | h'
  · subst k; rw [Nat.stirlingSecond_self, n.sub_self]; simp [Sym.eq_nil_of_card_zero]
  symm; calc ∑ s ∈ (range (k + 2)).sym (n - k), s.toMultiset.prod
    _ = ∑ s ∈ (range (k + 2)).sym (n - k.succ).succ with h : k + 1 ∈ s, s.toMultiset.prod
      + ∑ s ∈ (range (k + 2)).sym (n - k) with k + 1 ∉ s, s.toMultiset.prod := by
        rw [show (n - k.succ).succ = n - k by lia]; simp [← sum_filter, sum_filter_add_sum_filter_not]
    _ = ∑ s ∈ (range (k + 2)).sym (n - k.succ), ((k + 1) ::ₛ s).toMultiset.prod + _ := by
      congr 1; symm; apply sum_of_injOn (Sym.cons (k + 1)) (by simp)
      · simp [Set.MapsTo, -sym_succ]
      · simp [-sym_succ]; intro s hs h' h; contrapose! h'; exists s.erase (k + 1) h; simp
        intro a ha; exact hs a (Multiset.mem_of_mem_erase ha)
      · simp
    _ = (k + 1) * n.stirlingSecond (k + 1) + n.stirlingSecond k := by
      simp [Sym.coe_cons, ← mul_sum, ih h', ih h] ; congr; ext s; simp; grind



theorem Zad5b (h : k ≤ n) : Nat.stirlingFirst n k =
    ∑ s ∈ (range n).powersetCard (n - k), ∏ m ∈ s, m := by
  induction n generalizing k
  · rw [nonpos_iff_eq_zero] at h; subst h; simp
  rename_i n ih; cases k
  · rw [Nat.stirlingFirst_succ_zero, ← card_range (n + 1 - 0), tsub_zero,
      powersetCard_self, sum_singleton, prod_range_succ', mul_zero]
  rename_i k; rw [add_le_add_iff_right] at h; simp only [Nat.reduceSubDiff]
  rcases h.eq_or_lt with h | h'
  · subst k; simp [Nat.stirlingFirst_self]
  rw [show n - k = (n - k.succ).succ by lia, range_add_one, powersetCard_succ_insert notMem_range_self,
    sum_union, show (n - k.succ).succ = n - k by lia, ← ih h, Nat.stirlingFirst_succ_succ, add_comm,
    add_right_inj, ih h', Finset.sum_image, Finset.mul_sum]
  · congr! with s hs; symm; simp at hs; exact prod_insert (notMem_mono hs.left notMem_range_self)
  · simp [Set.InjOn, insert_eq, -singleton_union]; intro x hx hx' y hy hy'
    rw [← disjUnion_eq_union, ← disjUnion_eq_union, disjUnion_inj_right]
      <;> simp [notMem_mono hx notMem_range_self, notMem_mono hy notMem_range_self]
  · simp [Finset.disjoint_right]; intro y x hx hx' h; subst h; simp [insert_subset_iff]
