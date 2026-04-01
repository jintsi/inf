import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Derangements.Finite

variable [DecidableEq α] [Fintype α]

theorem Finset.inf_filter {s : Finset ι} (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    s.inf (fun i => univ.filter (p i)) = ({a | ∀ i ∈ s, p i a} : Finset _) := by
  ext a; simp [Finset.mem_inf]

theorem Finset.inf_univ_filter [Fintype ι] (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    univ.inf (fun i => univ.filter (p i)) = ({a | ∀ i, p i a} : Finset _) := by
  simp [Finset.inf_filter]

namespace MD1.Cwi5

/-- The union version is already proven as `Finset.inclusion_exclusion_card_biUnion`,
so here's just the intersection version -/
theorem Zad1_inf (s : Finset ι) (S : ι → Finset α) :
    (s.inf S).card = ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card * (t.inf fun i => (S i)ᶜ).card := by
  simp [← Finset.inclusion_exclusion_card_inf_compl]

theorem Zad2 [DecidableEq β] [Fintype β] :
    Finset.card {f : α → β | f.Surjective} = ∑ j ∈ Finset.range (Fintype.card β + 1),
    (-1 : ℤ) ^ j * (Fintype.card β).choose j * (Fintype.card β - j) ^ Fintype.card α := by
  unfold Function.Surjective
  rw [← Finset.inf_univ_filter, Zad1_inf]
  simp_rw [Finset.powerset_univ, Finset.compl_filter, not_exists, Finset.inf_filter]
  calc
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * Finset.card {f : α → β | ∀ b ∈ t, ∀ a, ¬f a = b} := by
    congr!
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * Fintype.card (α → ↥tᶜ) := by
    congr! with t ht; symm; rw [← Fintype.card_congr Equiv.subtypePiEquivPi]
    apply Fintype.card_of_subtype; simp; grind only
  _ = ∑ t : Finset β, (-1 : ℤ) ^ t.card * ↑(Fintype.card β - t.card) ^ Fintype.card α := by simp
  _ = ∑ j ∈ Finset.range (Fintype.card β + 1),
      (-1 : ℤ) ^ j * (Fintype.card β).choose j * (Fintype.card β - j) ^ Fintype.card α := by
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card fun j => _ * (_ - j).cast ^ _]
    simp_rw [Finset.card_univ, Int.nsmul_eq_mul, ← mul_assoc, mul_comm (Nat.cast _)]
    congr! with j hj; simp_all

theorem Zad4 : numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  numDerangements_add_two n
