import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Inf.MD1.Cwi5
import Mathlib.Data.Multiset.Fintype

@[to_dual]
theorem Multiset.sup_mem_of_ne_zero [LinearOrder α] [OrderBot α] {s : Multiset α} (h : s ≠ 0)
    : s.sup ∈ s := by
  induction s using Multiset.induction
  case empty => contradiction
  case cons a s ih =>
    rw [sup_cons, max_def]; split
    case isFalse ha => simp
    case isTrue ha => by_cases! hs : s = 0 <;> simp_all

@[to_dual (attr := elab_as_elim)]
theorem Multiset.inf_induction [LinearOrder α] {p : Multiset α → Prop} (empty : p 0)
    (cons : ∀ a s, (∀ b ∈ s, a ≤ b) → p s → p (a ::ₘ s)) (s : Multiset α) : p s := by
  let l := s.sort
  suffices p l by simpa [l]
  have : l.Pairwise (· ≤ ·) := s.pairwise_sort _
  revert this; induction l with
  | nil => simpa
  | cons a l ih => simp [← cons_coe]; intro ha hl; apply cons <;> simp_all

namespace Nat.Partition

open Multiset

/-- The conjugate partition, as obtained by reflecting a partition's Ferrers diagram across its
main diagonal. -/
@[simps -isSimp]
def conj (p : Partition n) : Partition n where
  parts := (range (p.parts.sup)).map fun k => p.parts.countP (k < ·)
  parts_pos := by
    simp [countP_pos]; intro a ha; by_cases! h : p.parts = 0
    · simp_all
    · use p.parts.sup, sup_mem_of_ne_zero h
  parts_sum := by
    simp [← Finset.range_val, ← p.parts_sum]
    generalize p.parts = s
    induction s using Multiset.induction
    case empty => simp
    case cons a s ih =>
      simp [countP_cons, Finset.sum_add_distrib]; rw [add_comm]; congr
      · convert Finset.card_range a; ext; simp; tauto
      · rw [← ih]; symm; apply Finset.sum_subset (by simp)
        simp [countP_eq_zero]

@[simp]
theorem conj_conj {p : Partition n} : p.conj.conj = p := by
  ext1; simp only [conj_parts]
  have : (map (fun k => countP (fun x => k < x) p.parts) (range p.parts.sup)).sup = p.parts.card := by
    apply le_antisymm (by simp [countP_le_card])
    by_cases! h : p.parts = 0; · simp [h]
    apply le_sup; simp [countP_eq_card]
    obtain ⟨a, ha⟩ := exists_mem_of_ne_zero h
    use 0, (p.parts_pos ha).trans_le (le_sup ha), @p.parts_pos
  rw [this]; generalize p.parts = s; clear n p this; induction s using inf_induction with
  | empty => simp
  | cons a s ha ih =>
    simp; congr
    · simp [countP_map, ← Finset.range_val, ← Finset.filter_val]
      convert Finset.card_range a; ext x; simp
      suffices s.card < countP (x < ·) (a ::ₘ s) ↔ x < a by simp_all
      calc s.card < countP (x < ·) (a ::ₘ s)
        _ ↔ s.card + 1 ≤ _ := Iff.rfl
        _ ↔ _ = s.card + 1 := by rw [LE.le.ge_iff_eq]; grw [countP_le_card]; simp
        _ ↔ _ = (a ::ₘ s).card := by congr!; simp
      rw [countP_eq_card]; simp; intro hx b hb; exact hx.trans_le (ha b hb)
    refine Eq.trans ?_ ih
    simp [countP_map, ← Finset.range_val, ← Finset.filter_val]; congr! 4 with i hi k
    · by_cases h : k < a; case neg => simp [h]
      suffices countP (fun x => k < x) s = s.card by simp_all; grw [hi]
      simp [countP_eq_card]; intro b hb; exact h.trans_le (ha b hb)
    · simp_all; have : s ≠ 0 := by intro; simp_all
      exact ha s.sup (sup_mem_of_ne_zero this)

@[simp]
theorem card_conj_parts {p : Partition n} : p.conj.parts.card = p.parts.sup := by simp [conj_parts]

@[simp]
theorem sup_conj_parts {p : Partition n} : p.conj.parts.sup = p.parts.card := by
  rw [← card_conj_parts, conj_conj]

/-- `conj` is a bijection from the set of partitions to itself. -/
@[simps]
def conjEquiv : Partition n ≃ Partition n where
  toFun := conj
  invFun := conj
  left_inv _ := conj_conj
  right_inv _ := conj_conj

end Nat.Partition

open Nat.Partition Finset PowerSeries

namespace MD1.Cwi9

theorem Zad1a {n k : ℕ} : #{p : n.Partition | p.parts.card = k} = #{p : n.Partition | p.parts.sup = k} := by
  apply card_equiv conjEquiv; simp

alias Zad1b := card_odds_eq_card_distincts

theorem Zad1c {n k : ℕ} : #{p : (n + k).Partition | p.parts.card = k} = #(restricted n (· ≤ k)) := by
  rw [Zad1a]; apply card_bij'
  case i =>
    intro p hp; simp at hp; use p.parts.erase k
    case parts_pos => grw [Multiset.erase_subset]; exact @p.parts_pos
    case parts_sum =>
      by_cases h : p.parts = 0
      · suffices n + k = 0 by simp_all
        rw [← p.parts_sum]; simp [h]
      have := p.parts_sum ▸ p.parts.sum_erase (hp ▸ p.parts.sup_mem_of_ne_zero h)
      lia
  case j =>
    intro p _; by_cases hk : k = 0
    · simp [hk]; exact p
    use k ::ₘ p.parts <;> simp_all [p.parts_pos, p.parts_sum] <;> lia
  case hi => simp [restricted]; intro p hp i; grw [Multiset.erase_subset]; intro hi; grw [p.parts.le_sup hi, hp]
  case hj =>
    split
    case isFalse => simp [restricted]
    subst k; simp [restricted]; intro a ha; rw [← nonpos_iff_eq_zero, Multiset.sup_le]; simpa
  case left_inv =>
    split
    case isTrue =>
      subst k; simp [Nat.Partition.ext_iff]; intro p hp
      apply p.parts.erase_of_notMem; convert p.parts_pos; simp
    case isFalse hk =>
      simp [Nat.Partition.ext_iff]; intro p hp; apply p.parts.cons_erase
      nth_rw 2 [← hp]; apply p.parts.sup_mem_of_ne_zero; intro; simp_all
  case right_inv =>
    split
    case isFalse => simp
    subst k; simp [Nat.Partition.ext_iff]; intro p hp
    apply p.parts.erase_of_notMem; convert p.parts_pos; simp

/- TODO: `Zad1d` -/

open scoped PowerSeries.WithPiTopology

section variable [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]

theorem Zad2a : (mk fun n => (Fintype.card n.Partition : R))
    = ∏' (i : ℕ), ∑' (j : ℕ), X ^ ((i + 1) * j) := by
  convert genFun_eq_tprod fun _ _ => (1 : R) with i
  · ext; simp
  rw [tsum_eq_zero_add']; · simp
  simpa using summable_genFun_term (fun _ _ => (1 : R)) i

omit [IsTopologicalSemiring R] in
theorem Zad2b : (mk fun n => (#(distincts n) : R)) = ∏' (i : ℕ), (1 + X ^ (i + 1)) := by
  simp [← countRestricted_two, powerSeriesMk_card_countRestricted_eq_tprod, sum_range_succ]

theorem Zad2c : (mk fun n => (#(odds n) : R))
    = ∏' (i : ℕ), if Odd (i + 1) then ∑' (j : ℕ), X ^ ((i + 1) * j) else 1 := by
  simp [odds, powerSeriesMk_card_restricted_eq_tprod]

theorem Zad2d : (mk fun n => (#(restricted n Even) : R))
    = ∏' (i : ℕ), if Even (i + 1) then ∑' (j : ℕ), X ^ ((i + 1) * j) else 1 :=
  powerSeriesMk_card_restricted_eq_tprod _ _

theorem Zad2e : (mk fun n => (#(restricted n (· ≤ m)) : R))
    = ∏ i ∈ range m, ∑' (j : ℕ), X ^ ((i + 1) * j) := by
  simp +contextual [powerSeriesMk_card_restricted_eq_tprod, tprod_eq_prod (s := range m),
      ← Nat.Ico_zero_eq_range, prod_ite]

omit [IsTopologicalSemiring R] in
theorem Zad2f : (mk fun n => (#{p : n.Partition | ∀ i ∈ p.parts, p.parts.count i ≤ m} : R))
    = ∏' (i : ℕ), ∑ j ∈ range (m + 1), X ^ ((i + 1) * j) := by
  simp [← powerSeriesMk_card_countRestricted_eq_tprod, countRestricted]

end

theorem Zad6_hasSum [CommSemiring R] [TopologicalSpace R]
    : HasSum (fun m => (mk fun n => (n : R)) ^ m)
    (mk fun n => ∑ m ∈ range (n + 1), ∑ k ∈ (range m).finsuppAntidiag n, ∏ i ∈ range m, k i) := by
  rw [WithPiTopology.hasSum_iff_hasSum_coeff]; intro n; simp [coeff_pow]
  apply hasSum_sum_of_ne_finset_zero; simp; intro m hm
  norm_cast; rw [← Nat.cast_zero]; congr
  apply sum_eq_zero; simp [Finset.subset_iff]; intro k hk _
  contrapose! hk; simp [-ne_eq, Finset.prod_ne_zero_iff] at hk
  suffices (range m).card • 1 ≤ (range m).sum k by simp at this; lia
  apply card_nsmul_le_sum; simp_all [Nat.one_le_iff_ne_zero]

theorem Zad6_eq_tsum [CommSemiring R] [TopologicalSpace R] [T2Space R] :
    (mk fun n => ∑ m ∈ range (n + 1), ∑ k ∈ (range m).finsuppAntidiag n, ∏ i ∈ range m, (k i : R))
    = ∑' (m : ℕ), (mk fun n => (n : R)) ^ m := Zad6_hasSum.tsum_eq.symm

theorem Zad6_eq_inv [CommRing R] [TopologicalSpace R] [T2Space R] [IsTopologicalRing R] :
    (mk fun n => ∑ m ∈ range (n + 1), ∑ k ∈ (range m).finsuppAntidiag n, ∏ i ∈ range m, (k i : R))
    * (1 - mk fun n => (n : R)) = 1 := by
  rw [mul_comm, Zad6_eq_tsum]
  apply WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero; simp

/-
theorem Zad6 [CommRing R] :
    (mk fun n => ∑ m ∈ range (n + 1), ∑ k ∈ (range m).finsuppAntidiag n, ∏ i ∈ range m, (k i : R))
    * (1 - mk fun n => (n : R)) = 1 := by
  ext n; simp [coeff_mul]; cases n with
  | zero => simp
  | succ n =>
    simp [Nat.antidiagonal_eq_map']; rw [sum_range_succ']; simp [-neg_add_rev, neg_add_eq_zero]
    sorry
-/

theorem Zad7 [CommRing R] (k : ℕ) :
    (mk fun n => n.stirlingSecond k : R⟦X⟧) = X ^ k * ∏ i ∈ range k, rescale (i + 1 : R) (mk 1) := by
  trans X ^ k * ∏ i ∈ range (k + 1), rescale (i : R) (mk 1); swap
  · simp [prod_range_succ']
  ext n; simp [coeff_X_pow_mul']; split
  case isFalse hk => simp_all [Nat.stirlingSecond_eq_zero_of_lt]
  case isTrue hk =>
    simp [coeff_prod]; norm_cast; congr; rw [Cwi5.Zad5a hk]
    apply sum_bij' (fun s _ => s.toMultiset.toFinsupp) (fun f hf => ⟨f.toMultiset, by
        rw [mem_finsuppAntidiag'] at hf; simpa using hf.left⟩)
    · simp [Sym.ext_iff] --left_neg (epic @[to_additive] fail)
    · simp --right_neg
    · simp [Multiset.prod_eq_prod_toEnumFinset, Multiset.toEnumFinset]
      intro s hs; rw [← prod_fiberwise_of_maps_to' (g := Prod.fst) (f := fun x => x)]
      · simp; congr! with i hi; trans #(range (s.toMultiset.count i)); swap; simp
        apply card_nbij' Prod.snd (i, ·) <;> simp_all [Set.MapsTo, Set.LeftInvOn]
        intro _ _ _ rfl; assumption
      · simp; intro a b h; apply hs; rw [← Sym.mem_coe, ← Multiset.count_pos]; lia
    · simp +contextual [-mem_finsuppAntidiag, mem_finsuppAntidiag', Finset.subset_iff]
      intro s hs; change s.toMultiset.toFinsupp.sum (fun x => id) = n - k; simp
    · simp [Finset.subset_iff]
