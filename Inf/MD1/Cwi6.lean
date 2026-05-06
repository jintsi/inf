import Mathlib.Order.Height
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Monovary
import Mathlib.Order.Interval.Basic
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Sups
import Mathlib.Tactic.Peel
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.SetFamily.LYM

open Finset Fintype

open Classical in
/-- If all chains in a partially ordered set have length `r` or less, and all antichains `s` or
less, then the poset has a cardinality of at most `r * s`. -/
theorem card_le_mul_of_isChain_isAntichain [Fintype α] [DecidableEq α] [PartialOrder α] {r s : ℕ}
    (hr : ∀ t : Finset α, IsChain (· ≤ ·) (SetLike.coe t) → #t ≤ r)
    (hs : ∀ t : Finset α, IsAntichain (· ≤ ·) (SetLike.coe t) → #t ≤ s) : card α ≤ r * s := by
  have hle : ∀ x : α, (Set.Iic x).chainHeight (· ≤ ·) ≤ r := by
    intro x; simp [Set.chainHeight]; intro t _ ht; specialize hr t.toFinset (by simpa)
    rw [Set.encard_eq_coe_toFinset_card]; simpa using hr
  have ha : ∀ i : ℕ, IsAntichain (· ≤ ·) {x : α | (Set.Iic x).chainHeight (· ≤ ·) = i} := by
    simp [IsAntichain, Set.Pairwise]; intro i x hx y hy hne hle
    let ⟨t, ht1, ht2, ht3⟩ := Set.exists_isChain_of_le_chainHeight _ (ge_of_eq hx)
    have := ht3.insert fun z hz _ => Or.inr (le_trans (ht1 hz) hle)
    absurd Set.encard_le_chainHeight_of_isChain (Set.Iic y) _ ?_ this
    · simp [Set.insert_subset_iff]; grw [ht1, hle]
    rw [not_le, hy, ← ht2, Set.encard_insert_of_notMem, ht2, ENat.lt_coe_add_one_iff]
    grw [ht1]; simpa using not_le_of_gt (lt_of_le_of_ne hle hne)
  rw [mul_comm, ← Nat.add_one_sub_one r, ← Nat.card_Icc]
  apply card_le_mul_card_image_of_maps_to (f := fun x => ((Set.Iic x).chainHeight (· ≤ ·)).toNat)
  · simp only [mem_univ, mem_Icc, forall_const]; intro x; and_intros
    · rw [← ENat.toNat_one]; apply ENat.toNat_le_toNat (by simp)
      apply Set.chainHeight_ne_top_of_finite; apply Set.toFinite
    · exact ENat.toNat_le_of_le_coe (hle x)
  · simp_rw [mem_Icc]; intro i hi; apply hs
    simp_rw [ENat.toNat_eq_iff (one_pos.trans_le hi.left).ne', coe_filter_univ]; exact ha i

theorem exists_isChain_or_isAntichain_of_mul_lt_card [Fintype α] [DecidableEq α] [PartialOrder α]
    {r s : ℕ} (h : r * s < card α) : (∃ t : Finset α, IsChain (· ≤ ·) (SetLike.coe t) ∧ r < #t)
    ∨ ∃ t : Finset α, IsAntichain (· ≤ ·) (SetLike.coe t) ∧ s < #t := by
  contrapose! h; exact card_le_mul_of_isChain_isAntichain h.1 h.2

/-- **Erdős–Szekeres Theorem**: A sequence of more than `r * s` distinct values has an
increasing subsequence of length longer than `r` or a decreasing subsequence of length longer than
`s`. -/
theorem erdos_szekeres [Fintype α] [LinearOrder α] [LinearOrder β]
    {r s : ℕ} (hn : r * s < card α) {f : α → β} (hf : f.Injective) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨ ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  let P := (univ : Finset α).map ⟨fun x => (x, f x), fun _ _ h => (Prod.mk.inj h).left⟩
  have hP : r * s < card ↥P := by simpa [P]
  rcases exists_isChain_or_isAntichain_of_mul_lt_card hP with ⟨t, ht, hr⟩ | ⟨t, ht, hs⟩
  · left; exists t.map ⟨fun x => x.val.1, by simp [Function.Injective, P]⟩
    simp [hr, StrictMonoOn, P]; intro x hx y hy h
    exact lt_of_le_of_ne (by simpa [h.le, h] using ht.le_of_not_gt hy hx) (hf.ne h.ne)
  · right; exists t.map ⟨fun x => x.val.1, by simp [Function.Injective, P]⟩
    simp [hs, StrictAntiOn, P]; intro x hx y hy h
    exact lt_of_le_of_ne' (by simpa [h.le] using ht.not_lt hx hy : _ ∧ _).right (hf.ne h.ne)

lemma Equiv.strictMonoOn_trans_iff [PartialOrder α] {f : α ≃ β} {g : β ≃ α} {s : Set α} :
    StrictMonoOn (f.trans g) s ↔ MonovaryOn g f.symm (f '' s) := by
  simp [MonovaryOn]; constructor
  · intro h a ha b hb hab; apply le_of_lt; simpa using h ha hb hab
  · refine fun h => MonotoneOn.strictMonoOn_of_injOn ?_ (f.trans g).injective.injOn
    intro a ha b hb hab; rcases eq_or_lt_of_le hab with rfl | hab
    · rfl
    · apply h <;> simpa

namespace MD1.Cwi6

theorem Zad1 (h : k ^ 3 < n) (σ₁ σ₂ σ₃ : Equiv.Perm (Fin n)) : ∃ s : Finset (Fin n), k < #s ∧
    (MonovaryOn σ₁.symm σ₂.symm s ∨ MonovaryOn σ₁.symm σ₃.symm s ∨ MonovaryOn σ₂.symm σ₃.symm s) := by
  rw [pow_three, ← Fintype.card_fin n] at h
  rcases erdos_szekeres h (σ₂.trans σ₁.symm).injective with ⟨s, hk, hs⟩ | ⟨s, hk, hs⟩
  · use s.map σ₂; simp_all [← Equiv.strictMonoOn_trans_iff]
  rw [← card_map (σ₂.trans σ₃.symm).toEmbedding, ← card_coe] at hk
  rcases erdos_szekeres hk (Subtype.restrict_injective _ (σ₃.trans σ₁.symm).injective)
      with ⟨t, hk, ht⟩ | ⟨t, hk, ht⟩
  · use ((t.map (Function.Embedding.subtype _))).map σ₃
    simp_all [← Equiv.strictMonoOn_trans_iff, StrictMonoOn, -Equiv.trans_toEmbedding]
  have hs' : StrictAntiOn (σ₁.trans σ₂.symm) (s.map (σ₂.trans σ₁.symm).toEmbedding) := by
    simp [StrictAntiOn, -Equiv.trans_toEmbedding]; intro x hx y hy; rw [← hs.lt_iff_gt hx hy]; simp
  have := hs'.comp ht (by simp [Set.MapsTo, -Equiv.trans_toEmbedding]; intro x h _; exists _, h; simp)
  use ((t.map (Function.Embedding.subtype _))).map σ₃
  simp_all [← Equiv.strictMonoOn_trans_iff, StrictMonoOn, -Equiv.trans_toEmbedding]

local instance Zad2.le [Preorder α] : LE (NonemptyInterval α) where
  le x y := x.snd < y.fst ∨ x = y

@[simp]
lemma Zad2.le_def [Preorder α] {x y : NonemptyInterval α} : x ≤ y ↔ x.snd < y.fst ∨ x = y := Iff.rfl

local instance Zad2.preorder [Preorder α] : Preorder (NonemptyInterval α) where
  lt x y := x.snd < y.fst
  le_refl x := .inr rfl
  le_trans x y z := by
    rintro (hxy | rfl) (hyz | rfl) <;> simp_all; left; exact (hxy.trans_le y.2).trans hyz
  lt_iff_le_not_ge x y := by
    constructor
    · intro h; simp [h, y.ext_iff, Prod.ext_iff]; use lt_asymm ((x.2.trans_lt h).trans_le y.2)
      intro h2; absurd h; rw [h2]; exact x.2.not_gt
    · simp +contextual [or_imp]

@[simp]
lemma Zad2.lt_def [Preorder α] {x y : NonemptyInterval α} : x < y ↔ x.snd < y.fst := Iff.rfl

local instance Zad2.partialOrder [Preorder α] : PartialOrder (NonemptyInterval α) where
  le_antisymm x y := by
    simp +contextual [or_imp]; intro h1 h2; exfalso
    exact lt_asymm (h1.trans_le y.2) (h2.trans_le x.2)

theorem Zad2 [LinearOrder α] {F : Finset (NonemptyInterval α)} (h : k ^ 2 < #F) :
    (∃ s ⊆ F, Set.PairwiseDisjoint (SetLike.coe s) (fun x => (x : Set α)) ∧ k < #s) ∨
    (∃ s ⊆ F, (s.inf fun x => (x : Set α)).Nonempty ∧ k < #s) := by
  have hF : k * k < card ↥F := by simpa [sq] using h
  rcases exists_isChain_or_isAntichain_of_mul_lt_card hF with ⟨s, hs, hk⟩ | ⟨s, hs, hk⟩
  · left; exists s.map (Function.Embedding.subtype _); use map_subtype_subset s
    simp [hk, Set.pairwiseDisjoint_iff, NonemptyInterval.coe_def, Set.Icc_inter_Icc]
    intro x _ hx y _ hy _ hyx hxy _
    exact le_antisymm (hs.le_of_not_gt hy hx hxy.not_gt) (hs.le_of_not_gt hx hy hyx.not_gt)
  · right; exists s.map (Function.Embedding.subtype _); use map_subtype_subset s; simp [hk]
    rcases s.eq_empty_or_nonempty with rfl | H
    · simp_all
    use s.sup' H fun x => x.val.fst; intro x _ hx; simp [x.mem_def]
    use ⟨x, ⟨‹_›, hx⟩, le_rfl⟩; intro y _ hy; simpa using hs.not_lt hx hy


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

theorem Zad5ii_le (hF : Pairwise fun x y => ∃ s ∈ F, x ∈ s ∧ y ∉ s) : card α ≤ (#F).choose (#F / 2) := by
  have : Function.Injective fun x => ({s | x ∈ s.val} : Finset F) := by
    rw [Function.injective_iff_pairwise_ne]
    exact hF.mono (by simp [Function.onFun, Finset.ext_iff]; grind only)
  rw [Fintype.card, ← card_image_of_injective _ this, ← card_coe F]; apply IsAntichain.sperner
  simp_all [IsAntichain, Set.Pairwise, -univ_eq_attach, this.eq_iff, Finset.subset_iff,
    Pairwise, and_assoc]

theorem Zad6 (hr : (SetLike.coe F).Sized r) (hs : (Set.Iio s).IsIntersectingOf (SetLike.coe F)) :
    #F * r.choose s ≤ (card α).choose s := calc
  #F * r.choose s = ∑ a ∈ F, #(a.powersetCard s) := by
    symm; apply sum_const_nat; simp [Set.Sized] at hr; simp +contextual [hr]
  _ = #(F.biUnion (powersetCard s)) := by
    symm; apply card_biUnion; refine hs.mono' ?_; simp_rw [Set.mem_Iio]; intro a b h
    simp [disjoint_left]; intro x ha rfl hb; contrapose! h; exact card_le_card (subset_inter ha hb)
  _ ≤ #(univ.powersetCard s) := card_le_card (by simp)
  _ = (card α).choose s := by simp
