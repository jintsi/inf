import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

open Finset

theorem Finpartition.card_of_parts [DecidableEq α] (s : Finset α) (k : ℕ) :
    Finset.card {P : Finpartition s | P.parts.card = k} = s.card.stirlingSecond k := by
  induction s using Finset.induction generalizing k
  case empty =>
    rcases k with (_ | k)
    · suffices Fintype.card (Finpartition ∅) = 1 by simpa
      rw [Fintype.card_eq_one_iff_nonempty_unique]; exact ⟨instUniqueBot⟩
    case succ => simp; intro P; convert k.zero_ne_add_one; rw [← Nat.le_zero]; exact P.card_parts_le_card
  rename_i a s ha ih
  cases k; case zero => simp [ha]
  rename_i k; simp [ha, Nat.stirlingSecond_succ_succ]
  calc Finset.card {P : Finpartition (insert a s) | P.parts.card = k + 1}
  _ = Finset.card {P : Finpartition (insert a s) | P.parts.card = k + 1 ∧ P.part a = {a}} +
      Finset.card {P : Finpartition (insert a s) | P.parts.card = k + 1 ∧ P.part a ≠ {a}} := by
    simp [Finset.filter_and_not, Finset.filter_and]
  _ = Finset.card {P : Finpartition s | P.parts.card = k} + _ := by
    congr 1; symm; apply Finset.card_nbij fun P => P.extendOfLE (by simp)
      <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def]
    · intro P hP; suffices {a} ∉ P.parts by
        rw [part_eq_iff_mem] <;> simp [P.parts_extendOfLE_of_lt (Finset.ssubset_insert ha), *]
      intro this; apply P.subset at this; simp [ha] at this
    · intro P₁ hP₁ P₂ hP₂ h; ext1
      rwa [Finpartition.ext_iff, P₁.parts_extendOfLE_of_lt (Finset.ssubset_insert ha),
        P₂.parts_extendOfLE_of_lt (Finset.ssubset_insert ha), Finset.insert_sdiff_cancel ha,
        Finset.Subset.antisymm_iff, Finset.insert_subset_insert_iff, Finset.insert_subset_insert_iff,
        ← Finset.Subset.antisymm_iff] at h
      all_goals (intro this; apply Finpartition.subset at this; simp [ha] at this)
    · intro P hP hPa; use P.restrict (Finset.subset_insert a s)
      have : (P.restrict (Finset.subset_insert a s)).parts = P.parts.erase {a} := by
        simp [restrict]; ext x; simp only [Finset.mem_erase, Finset.mem_image]; constructor
        · intro ⟨h₁, x', h₂, h₃⟩; by_cases h : a ∈ x'
          · absurd h₁; rw [← P.part_eq_iff_mem h₂, hPa] at h; subst h h₃; simp [ha]
          · suffices x = x' by rw [← P.part_eq_iff_mem h₂, hPa, eq_comm] at h; simp_all
            subst h₃; simpa using ((Finset.subset_insert_iff_of_notMem h).mp (P.subset h₂))
        · intro ⟨h₁, h₂⟩; use P.ne_empty h₂, x, h₂; rw [← hPa, ne_comm, Ne, P.part_eq_iff_mem h₂] at h₁
          simpa using ((Finset.subset_insert_iff_of_notMem h₁).mp (P.subset h₂))
      and_intros
      · simp [this, Finset.card_erase_of_mem, ← hPa, hP, k.add_one_sub_one]
      · ext1; rw [fun P => parts_extendOfLE_of_lt P (Finset.ssubset_insert ha), this]
        simp [ha, ← hPa]
  _ = s.card.stirlingSecond k + _ := congrArg (· + _) (ih k)
  _ = _ + ∑ t ∈ {P : Finpartition s | P.parts.card = k + 1}, Finset.card {P | P.parts.card = k + 1
      ∧ P.part a ≠ {a} ∧ restrict P (Finset.subset_insert a s) = t} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun P => restrict P (Finset.subset_insert a s))]
    congr! 3 with t ht
    · simp [Finset.filter_filter, and_assoc]
    · simp [Set.MapsTo, restrict]; intro P h₁ h₂
      have : ∀ x ∈ P.parts, (x ∩ s).Nonempty := by
        intro x hx; contrapose! h₂ with this; rw [← Finset.disjoint_iff_inter_eq_empty] at this
        replace := Finset.subset_sdiff.mpr ⟨P.subset hx, this⟩
        simp [ha, (P.nonempty_of_mem_parts hx).ne_empty] at this
        apply P.part_eq_of_mem (by rwa [← this]) (by simp)
      rwa [Finset.erase_eq_of_notMem, Finset.card_image_of_injOn]
      · simp [Set.InjOn]; intro x hx y hy h; have ⟨i, hi⟩ := this x hx
        rw [← P.part_eq_of_mem hx (Finset.mem_of_mem_inter_left hi),
            ← P.part_eq_of_mem hy (Finset.mem_of_mem_inter_left (h ▸ hi))]
      · simpa [Finset.nonempty_iff_ne_empty] using this
  _ = _ + ∑ t ∈ {P : Finpartition s | P.parts.card = k + 1}, t.parts.card := by
    congr! with t ht; apply Finset.card_bij' (fun P _ => P.part a ∩ s) fun p hp => ofExistsUnique
      (t.parts.image fun x => if x = p then insert a x else x)
      (by simp; intro x hx; have := t.subset hx; split <;> grind) (by
        simp; and_intros
        · use! insert a p, p, hp, by simp, (by simp); rintro _ ⟨⟨y, hy, rfl⟩, hay⟩
          suffices y = p by simp [this]
          by_contra; simp_all; grind [t.subset hy]
        · intro x hx; use! (fun x => if x = p then insert a x else x) (t.part x), t.part x,
            by simp [hx], (by dsimp; split <;> simp [hx]); rintro _ ⟨⟨y, hy, rfl⟩, hxy⟩
          suffices y = t.part x by simp [this]
          have : x ∈ y := by split at hxy <;> simp_all [ne_of_mem_of_not_mem hx ha]
          symm; exact t.part_eq_of_mem hy this)
      (by simp; intro x hx; split <;> simp [t.ne_empty hx])
    · simp; intro P hP hPa hPt; rw! [← hPt]; ext1; simp [restrict]; rw [Finset.erase_eq_of_notMem]
      · simp [Finset.image_image]; rw [Finset.image_congr]; exact Finset.image_id'
        simp [Set.EqOn]; intro x hx; split <;> rename_i hxs
        · suffices h : P.part a = x by
            rw [← h, ← Finset.inter_insert_of_mem, Finset.inter_eq_left] <;> simp
          have ⟨b, hb, hba⟩ := Finset.nontrivial_iff_ne_singleton (P.mem_part (Finset.mem_insert_self a s))
            |>.mpr hPa |>.exists_ne a
          apply P.eq_of_mem_parts (by simp) hx hb
          have := Finset.mem_inter_of_mem hb (s.mem_of_mem_insert_of_ne (P.part_subset a hb) hba)
          exact Finset.mem_of_mem_inter_left (hxs ▸ this)
        · simp; contrapose hxs with this; rw [Finset.not_subset] at this; have ⟨b, hbx, hbs⟩ := this
          replace := s.eq_of_mem_insert_of_notMem (P.subset hx hbx) hbs
          subst this; congr; symm; exact P.part_eq_of_mem hx hbx
      · simp [Finset.ext_iff]; intro x hx; by_cases h : P.part a = x
        · subst h; have ⟨b, hb, hba⟩ := Finset.nontrivial_iff_ne_singleton (P.mem_part
            (Finset.mem_insert_self a s)) |>.mpr hPa |>.exists_ne a
          exact ⟨b, hb, s.mem_of_mem_insert_of_ne (P.part_subset a hb) hba⟩
        · have ⟨b, hb⟩ := P.nonempty_of_mem_parts hx; use b, hb
          apply s.mem_of_mem_insert_of_ne (P.subset hx hb); by_contra; subst this
          exact h (P.part_eq_of_mem hx hb)
    · intro p hp
      generalize hP : ofExistsUnique (Finset.image (fun x => if x = p then _ else x) t.parts) _ _ _ = P
      suffices P.part a = insert a p by simpa [this, ha] using t.subset hp
      apply P.part_eq_of_mem <;> simp [← hP]; use p, hp; simp
    · simp; intro P hP hPa hPt; rw [← hPt]; simp [restrict]; and_intros
      · have ⟨b, hb, hba⟩ := Finset.nontrivial_iff_ne_singleton (P.mem_part (Finset.mem_insert_self a s))
          |>.mpr hPa |>.exists_ne a
        simp [Finset.ext_iff]; exact ⟨b, hb, s.mem_of_mem_insert_of_ne (P.part_subset a hb) hba⟩
      · use P.part a; simp
    · simp [restrict, Finpartition.ext_iff, Finset.image_image]; intro p hp; and_intros
      · simp at ht; rw [← ht, Finset.card_image_iff]; simp [Set.InjOn]
        intro x hx y hy h; apply_fun (· \ {a}) at h; convert h
        all_goals split; simp [Finset.insert_sdiff_of_mem]; all_goals
          symm; simp [Finset.sdiff_singleton_eq_erase]; exact Finset.notMem_mono (t.subset ‹_›) ha
      · generalize hP : ofExistsUnique (Finset.image (fun x => if x = p then _ else x) t.parts) _ _ _ = P
        suffices {a} ∉ P.parts by contrapose this; simp [← this]
        subst hP; simp; intro x hx; split
        simp [← Finset.singleton_union, ← Finset.not_nonempty_iff_eq_empty, t.nonempty_of_mem_parts hx]
        all_goals contrapose ha; subst ha; simpa using t.subset hx
      · rw [Finset.erase_eq_of_notMem, Finset.image_congr]; exact Finset.image_id'
        · simp [Set.EqOn]; intro x hx; split; rw [Finset.insert_inter_of_notMem ha]
          all_goals simpa using t.subset hx
        · simp; intro x hx; split; rw [Finset.insert_inter_of_notMem ha]
          all_goals simpa [Finset.inter_eq_left.mpr (t.subset hx)] using t.ne_empty hx
  _ = _ + Finset.card {P : Finpartition s | P.parts.card = k + 1} * (k + 1) := by
    congr; apply Finset.sum_const_nat; simp
  _ = s.card.stirlingSecond k + s.card.stirlingSecond (k + 1) * (k + 1) := by rw [ih]
  _ = (k + 1) * s.card.stirlingSecond (k + 1) + s.card.stirlingSecond k := by ring

@[simp]
theorem Finpartition.card [DecidableEq α] (s : Finset α) :
    Fintype.card (Finpartition s) = s.card.bell := by
  induction s using Finset.case_strong_induction_on
  case h₀ => rw [Finset.card_empty, Nat.bell_zero,
    Fintype.card_eq_one_iff_nonempty_unique]; exact ⟨instUniqueBot⟩
  case h₁ a s ha ih => calc Fintype.card (Finpartition (insert a s))
    _ = ∑ t ∈ s.powerset, Finset.card {P : Finpartition (insert a s) | P.part a \ {a} = t} :=
      Finset.card_eq_sum_card_fiberwise (by simp; norm_cast; simp)
    _ = ∑ t ∈ s.powerset, Finset.card {P : Finpartition (insert a s) | P.part a = insert a t} := by
      congr! 3 with t ht P; constructor
      · intro rfl; simp
      · intro h; rw [h]; simp [Finset.insert_sdiff_of_mem]
        rw [Finset.mem_powerset] at ht; exact Finset.notMem_mono ht ha
    _ = ∑ t ∈ s.powerset, Fintype.card (Finpartition (insert a s \ insert a t)) := by
      congr! with t ht; rw [Finset.mem_powerset] at ht; symm
      have hlt : insert a s \ insert a t < insert a s := by
        simpa using Finset.ssubset_of_subset_of_ssubset Finset.sdiff_subset (Finset.ssubset_insert ha)
      apply Finset.card_nbij fun P => P.extendOfLE Finset.sdiff_subset
        <;> simp [Set.SurjOn, Set.subset_def]
      · intro P; refine part_eq_of_mem ?_ ?_ (t.mem_insert_self a)
        rw [P.parts_extendOfLE_of_lt hlt, Finset.sdiff_sdiff_eq_self] <;> simp [ht]
      · simp only [Function.Injective, Finpartition.ext_iff, fun P => parts_extendOfLE_of_lt P hlt]
        intro P₁ P₂ h; apply_fun (· \ {insert a t}) at h; convert h; all_goals
          symm; rw [Finset.sdiff_sdiff_eq_self (by simp [ht])]; simp [Finset.insert_sdiff_of_mem]
          intro this; apply Finpartition.subset at this; simp at this
      · intro P hP; use ofExistsUnique (P.parts \ {insert a t}) (by
          simp_rw [Finset.mem_sdiff, Finset.mem_singleton, ← hP]
          intro p ⟨hp, hnp⟩ x hx; have := P.subset hp hx
          rw [Finset.mem_sdiff, P.mem_part_iff_part_eq_part this (by simp)]; use this
          exact ne_of_eq_of_ne (P.part_eq_of_mem hp hx) hnp) (by
          simp_rw [Finset.mem_sdiff, Finset.mem_singleton, ← hP]
          intro x ⟨hx, hnx⟩; use P.part x; simp [hx, part_eq_iff_mem, hnx]
          intro y hy _ hxy; symm; exact P.part_eq_of_mem hy hxy) (by simp)
        ext p; rw [fun P => parts_extendOfLE_of_lt P hlt,
          Finset.sdiff_sdiff_eq_self (Finset.insert_subset_insert a ht)]
        suffices p = insert a t → p ∈ P.parts by simp; tauto
        intro this; rw [this, ← hP]; simp
    _ = ∑ t ∈ s.powerset, Fintype.card (Finpartition (s \ t)) := by
      congr! 3 with t ht; simp; apply Finset.sdiff_insert_of_notMem ha
    _ = ∑ t ∈ s.powerset, (s \ t).card.bell := by congr with t; apply ih; simp
    _ = ∑ t ∈ s.powerset, (s.card - t.card).bell := by
      congr! with t ht; simp_all [Finset.card_sdiff_of_subset]
    _ = ∑ k ∈ Finset.range s.card.succ, s.card.choose k * (s.card - k).bell := by
      simpa using Finset.sum_powerset_apply_card fun k => Nat.bell _
    _ = (s.card + 1).bell := by
      rw [Nat.bell_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = (insert a s).card.bell := by simp [ha]

namespace MD1.Cwi3

theorem Zad1 (h : 0 < n) : n.bell = ∑ i ∈ range n, (n - 1).choose i * i.bell := by
  rw [show n = n - 1 + 1 by lia, Nat.add_one_sub_one,
    ← sum_flip, Nat.bell_succ, Nat.range_succ_eq_Iic]
  congr! 2 with i hi; exact (Nat.choose_symm (by simpa using hi)).symm

theorem Zad2 (n k : ℕ) : (n + 1).stirlingSecond (k + 1) = ∑ i ≤ n, n.choose i * i.stirlingSecond k := by
  induction n generalizing k with
  | zero => simp [← Nat.range_succ_eq_Iic, Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    rcases k with (- | k)
    · simp [Nat.stirlingSecond_one_right, ← Nat.range_succ_eq_Iic, sum_range_succ']
    symm; calc ∑ i ≤ n + 1, (n + 1).choose i * i.stirlingSecond (k + 1)
    _ = ∑ i ∈ range (n + 1), (n + 1).choose (i + 1) * (i + 1).stirlingSecond (k + 1) := by
      rw [← Nat.range_succ_eq_Iic, sum_range_succ']; simp
    _ = ∑ i ∈ range (n + 1), n.choose (i + 1) * (i + 1).stirlingSecond (k + 1)
      + ∑ i ∈ range (n + 1), n.choose i * (i + 1).stirlingSecond (k + 1) := by
      simp [Nat.choose_succ_succ, add_mul, sum_add_distrib, add_comm]
    _ = _ + (k + 1) * ∑ i ∈ range (n + 1), n.choose i * i.stirlingSecond (k + 1) +
        ∑ x ∈ range (n + 1), n.choose x * x.stirlingSecond k := by
      rw [add_assoc]; congr 1; simp [Nat.stirlingSecond_succ_succ, mul_add, sum_add_distrib]
      simp [← mul_left_comm (k + 1), ← mul_sum]
    _ = ∑ i ∈ range (n + 1), n.choose i * i.stirlingSecond (k + 1) + _ + _ := by
      congr 2; rw [sum_range_succ, sum_range_succ']; congr 1; simp
    _ = (k + 2) * ∑ i ≤ n, n.choose i * i.stirlingSecond (k + 1)
      + ∑ i ≤ n, n.choose i * i.stirlingSecond k := by
        rw [← add_comm (_ * _), ← add_one_mul, Nat.range_succ_eq_Iic]; rfl
    _ = (n + 2).stirlingSecond (k + 2) := by rw [Nat.stirlingSecond_succ_succ, ih, ih]

end MD1.Cwi3

/-
@[simp]
theorem Finpartition.card_of_parts' [DecidableEq α] (s : Finset α) (k : ℕ) :
    Finset.card {P : Finpartition s | #P.parts = k} = (#s).stirlingSecond k := by
  induction s using case_strong_induction_on generalizing k
  · rcases k with (- | k); case zero => simp
    case succ => simp; intro P; apply ne_of_lt; grw [P.card_parts_le_card]; simp
  rename_i a s ha ih; rcases k with (- | k); case zero => simp [ha]
  calc #{P : Finpartition (insert a s) | #P.parts = k + 1}
  _ = ∑ p ∈ s.powerset, #{P : Finpartition (insert a s) | #P.parts = k + 1 ∧ s \ (P.part a) = p} := by
    rw [card_eq_sum_card_fiberwise (f := fun P => s \ (P.part a))]; congr! 2; ext; simp
    intro P _; simp
  _ = ∑ p ∈ s.powerset, #{P : Finpartition p | #P.parts = k} := by
    congr! 1 with p hp; simp at hp; apply card_nbij' (fun P => P.restrict (by grw [hp]; simp))
      (fun P => P.extendOfLE (by grw [hp]; simp))
    · intro P; simp [restrict]; intro hk hp; rw [card_erase_of_mem, card_image_of_injOn, hk]; simp
      · intro x hx y hy h; simp [← hp] at h; sorry
      · simp; use P.part a; simp [← hp]
    · intro P; simp
      have := P.parts_extendOfLE_of_lt (a := p) (b := insert a s) (by grw [← ssubset_insert ha]; exact hp)
      rw [this, card_insert_of_notMem]; intro h; simp [h]; trans s \ (insert a s \ p)
      · congr; apply Finpartition.part_eq_of_mem _ (by simp [this]) (by simp; grw [hp]; exact ha)
      · simp [sdiff_sdiff_right', Finset.sdiff_insert_of_notMem ha, hp]
      · apply mt P.subset; simp [Finset.subset_iff]; grw [hp]; simpa
    · intro P; simp [Finpartition.ext_iff]
      have := (P.restrict (by grw [hp]; simp)).parts_extendOfLE_of_lt (a := p) (b := insert a s)
        (by grw [← ssubset_insert ha]; exact hp)
      rw [this, restrict]; simp; sorry
    · intro P; simp; sorry
  _ = ∑ p ∈ s.powerset, (#p).stirlingSecond k := by congr! with p hp; simp at hp; simp [ih, hp]
  _ = (#(insert a s)).stirlingSecond (k + 1) := by rw [sum_powerset_apply_card (f := fun m => m.stirlingSecond k),
      Nat.range_succ_eq_Iic, card_insert_of_notMem ha, MD1.Cwi3.Zad2]; rfl
-/

/-- The Bell triangle a_n,k. -/
def Nat.bellTrig (n k : ℕ) : ℕ :=
  match n, k with
  | 0, k => 2 ^ k
  | n + 1, 0 => n.bellTrig n
  | n + 1, k + 1 => n.bellTrig k + (n + 1).bellTrig k

lemma Nat.bellTrig_eq_sum_bell (n k : ℕ) :
    n.bellTrig k = ∑ i ∈ Finset.range (k + 1), k.choose i * (n + i - k).bell := by
  induction n generalizing k
  case zero => calc
    Nat.bellTrig 0 k = 2 ^ k := Nat.bellTrig.eq_1 k
    _ = ∑ i ∈ Finset.range (k + 1), k.choose i := k.sum_range_choose.symm
    _ = ∑ i ∈ Finset.range (k + 1), k.choose i * (0 + i - k).bell := by
      congr! 1 with i hi; simp_all
  induction k
  case zero n ih => simp [Nat.bellTrig, ih, MD1.Cwi3.Zad1]
  case succ n ih₁ k ih₂ =>
    rw [Nat.bellTrig, ih₁, ih₂]; symm; calc
      ∑ i ∈ Finset.range (k + 2), (k + 1).choose i * (n + 1 + i - (k + 1)).bell
      _ = ∑ i ∈ Finset.range (k + 2), (k + 1).choose i * (n + i - k).bell := by lia
      _ = ∑ i ∈ Finset.range (k + 1), k.choose i * (n + i - k).bell
        + ∑ i ∈ Finset.range (k + 1), k.choose i * (n + (i + 1) - k).bell :=
        Finset.sum_choose_succ_mul (fun _ _ => _) _
      _ = _ := by ac_rfl

namespace MD1.Cwi3

theorem Zad4 (n : ℕ) : n.bell = n.bellTrig 0 := by simp [Nat.bellTrig_eq_sum_bell]

alias Zad5 := BinaryTree.treesOfNumNodesEq_card_eq_catalan
