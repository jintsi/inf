import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Sups
import Mathlib.Tactic.Peel
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Group.Nat

open Finset Fintype

namespace MD1.Cwi6

variable [Fintype α] [DecidableEq α] {F : Finset (Finset α)}

theorem Zad3 [Nonempty α] {F : Finset (Finset α)}
    (hF : Maximal (fun s => (SetLike.coe s).Intersecting) F) : 2 * #F = 2 ^ card α := by
  rw [maximal_iff] at hF; rw [hF.left.is_max_iff_card_eq.mp hF.right, card_finset]

theorem Zad4 [Nonempty α] {F : Finset (Finset α)}
    (hF : Maximal (fun s => ∀ a ∈ s, ∀ b ∈ s, a ∪ b ≠ univ) F) : 2 * #F = 2 ^ card α := by
  suffices Maximal (fun s => (SetLike.coe s).Intersecting) (F.compls) by
    rw [← Zad3 this, card_compls]
  revert hF; unfold Maximal; apply And.imp
  · unfold Set.Intersecting; simp; intro h; peel h
    simpa [not_disjoint_iff_nonempty_inter, ← compl_union, nonempty_iff_ne_empty]
  · intro h s hs; rw [le_iff_subset, le_iff_subset, ← compls_subset_iff, compls_subset_iff]
    apply h; simp [-mem_compls, forall_mem_compls, ← compl_inter]
    simp [Set.Intersecting] at hs; peel hs
    rwa [not_disjoint_iff_nonempty_inter, nonempty_iff_ne_empty] at this

theorem Zad5i_le (hF : Pairwise fun x y => ∃ s ∈ F, ¬(x ∈ s ↔ y ∈ s)) : Nat.clog 2 (card α) ≤ #F := by
  rw [Nat.clog_le_iff_le_pow (by simp), ← card_powerset]
  apply card_le_card_of_injOn (fun x => {s ∈ F | x ∈ s}) (by simp [-coe_filter])
  rw [coe_univ, Set.injOn_univ, Function.injective_iff_pairwise_ne]
  exact hF.mono (by simp [Function.onFun, Finset.ext_iff])

theorem Zad5i_exists : ∃ (F : Finset (Finset α)), (Pairwise fun x y => ∃ s ∈ F, ¬(x ∈ s ↔ y ∈ s))
    ∧ #F = Nat.clog 2 (card α) := by
  obtain ⟨e⟩ := Fintype.truncEquivFin α
  exists (range (Nat.clog 2 (card α))).image fun i => ({x | (e x).val.testBit i} : Finset α)
  and_intros
  · simp; intro x y h; contrapose! h
    suffices (e x).val = (e y).val by simp_all [Fin.val_inj]
    apply Nat.eq_of_testBit_eq; intro i
    by_cases! hi : i < Nat.clog 2 (Fintype.card α)
    · exact h i hi
    · rw [Nat.clog_le_iff_le_pow (by simp)] at hi
      rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow] <;> exact hi.trans_lt' (Fin.is_lt _)
  rw [card_image_of_injOn, card_range]; simp [Set.InjOn, Finset.ext_iff, Nat.lt_clog_iff_pow_lt]
  intro x hx y hy h; contrapose! h; use e.symm ⟨2 ^ x, hx⟩; simp [h]

theorem Zad6 (hr : (SetLike.coe F).Sized r) (hs : (Set.Iio s).IsIntersectingOf (SetLike.coe F)) :
    #F * r.choose s ≤ (card α).choose s := calc
  #F * r.choose s = ∑ a ∈ F, #(a.powersetCard s) := by
    symm; apply sum_const_nat; simp [Set.Sized] at hr; simp +contextual [hr]
  _ = #(F.biUnion (powersetCard s)) := by
    symm; apply card_biUnion; refine hs.mono' ?_; simp_rw [Set.mem_Iio]; intro a b h
    simp [disjoint_left]; intro x ha rfl hb; contrapose! h; exact card_le_card (subset_inter ha hb)
  _ ≤ #(univ.powersetCard s) := card_le_card (by simp)
  _ = (card α).choose s := by simp
