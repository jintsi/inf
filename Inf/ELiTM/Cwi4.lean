import Mathlib.Algebra.Order.Archimedean.Basic

namespace Elitm.Cwi4

theorem Zad1a [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    [ExistsAddOfLE K] : ⋂ i : ℕ, Set.Ioo (0 : K) (1 / (i + 1)) = ∅ := by
  ext x; simp; by_cases hx : 0 < x <;> simp [hx, ← one_div]
  exact (exists_nat_one_div_lt hx).imp fun _ => le_of_lt

theorem Zad1b [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    [ExistsAddOfLE K] : ⋂ i : ℕ, Set.Ioc (0 : K) (1 / (i + 1)) = ∅ := by
  ext x; simp; by_cases hx : 0 < x <;> simp [hx, ← one_div]
  exact exists_nat_one_div_lt hx

theorem Zad1c [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    [ExistsAddOfLE K] : ⋂ i : ℕ, Set.Icc (0 : K) (1 / (i + 1)) = {0} := by
  ext x; simp; rcases lt_trichotomy x 0 with hx | rfl | hx
  · simpa [not_le_of_gt hx] using hx.ne
  · simp; intro i; positivity
  · simpa [hx.le, hx.ne'] using exists_nat_one_div_lt hx

theorem Zad1d [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] :
    ⋂ i : ℕ, Set.Ioi (i : R) = ∅ := by
  ext x; simpa using (exists_nat_ge x).imp fun _ => not_lt_of_ge

theorem Zad1e [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] :
    ⋂ i : ℕ, {(x, y) : K × K | x + y ≤ 1 / (i + 1)} = {(x, y) | x + y ≤ 0} := by
  ext p; simp; by_cases hp : p.1 + p.2 ≤ 0 <;> simp [hp, ← one_div]
  · intro i; grw [hp]; simp; positivity
  · exact exists_nat_one_div_lt (lt_of_not_ge hp)

theorem Zad1f [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    [ExistsAddOfLE K] : ⋂ i : ℕ, {(x, y) : K × K | 0 ≤ x ∧ 0 ≤ y ∧ y ≤ x ^ i} =
    Set.Ici 0 ×ˢ {0} ∪ Set.Ici 1 ×ˢ Set.Icc 0 1 := by
  ext ⟨x, y⟩; simp; constructor
  · intro h; rcases eq_or_lt_of_le (h 0).2.1 with rfl | hy; · simp [h 0]
    right; simp [hy.le, pow_zero x ▸ (h 0).2.2]; contrapose! h
    exact (exists_pow_lt_of_lt_one hy h).imp fun _ h _ _ => h
  · rintro (⟨hx, rfl⟩ | ⟨hx, hy⟩) i <;> grw [← hx] <;> simp; exact hy

theorem Zad2a [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α] :
    ⋃ i : ℕ, Set.Ioi (i : α) = Set.Ioi 0 := by
  ext x; constructor <;> simp
  · intro i h; grw [← h]; simp
  · intro h; use 0; simpa

theorem Zad2b [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] :
    ⋃ i : ℕ, Set.Ioc (1 / (i + 1 : K)) (1 - 1 / (i + 1)) = Set.Ioo 0 1 := by
  ext x; constructor <;> simp
  · intro i hl hu; grw [← hl, hu]; simp; and_intros <;> positivity
  · intro hl hu
    have ⟨n, hn⟩ := exists_nat_one_div_lt hl
    have ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos_of_lt hu)
    use max n m; and_intros
    · grw [← le_max_left, ← one_div]; assumption
    · grw [← le_max_right, le_sub_comm, ← one_div]; exact hm.le

theorem Zad2c [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    ⋃ i : ℕ, Set.Ioo (-i : R) i = Set.univ := by
  simp [Set.eq_univ_iff_forall]; intro x
  have ⟨n, hn⟩ := exists_nat_gt x; have ⟨m, hm⟩ := exists_nat_gt (-x)
  use max n m; grw [hn, neg_lt, hm]; simp

alias Zad2d := Zad2a

theorem Zad2e [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] :
    ⋃ i : ℕ, {(x, y) : R × R | x + y ≤ i} = Set.univ := by
  simp [Set.eq_univ_iff_forall]; intro x y; exact exists_nat_ge (x + y)

theorem Zad2f [Semifield K] [PartialOrder K] [AddLeftMono K] [ZeroLEOneClass K]
    [PosMulReflectLE K] [AddRightReflectLE K] :
    ⋃ i : ℕ, {(x, y) : K × K | x + y ≤ 1 / (i + 1)} = {(x, y) | x + y ≤ 1} := by
  ext p; constructor <;> simp
  · intro i h; grw [h]; apply inv_le_one_of_one_le₀; rw [le_add_iff_nonneg_left]; simp
  · intro h; use 0; simpa

theorem Zad2h [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
    [ExistsAddOfLE R] : ⋃ i : ℕ, {(x, y) : R × R | 0 ≤ x ∧ 0 ≤ y ∧ y ≤ x ^ i} =
    Set.Ici 0 ×ˢ Set.Icc 0 1 ∪ Set.Ioi 1 ×ˢ Set.Ici 0 := by
  ext ⟨x, y⟩; constructor <;> simp
  · intro hx hy n h; by_cases! hx' : 1 < x; · exact Or.inr ⟨hx', hy⟩
    left; use hx, hy; grw [h, hx', one_pow]
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩); · use hx, hy.1, 0, pow_zero x ▸ hy.2
    use zero_le_one.trans hx.le, hy; exact (pow_unbounded_of_one_lt y hx).imp fun _ => le_of_lt

-- TODO: Zad3

alias Zad5a := Set.iUnion_of_empty
alias Zad5b := Set.iInter_of_empty
alias Zad6a := Set.iUnion_inter_subset

theorem Zad6b {s t : ι → Set α} : (⋂ i, s i) ∪ ⋂ i, t i ⊆ ⋂ i, s i ∪ t i :=
  iInf_sup_iInf_le s t

theorem Zad6c {s t : ι → Set α} : ⋃ i, s i \ t i ⊆ (⋃ i, s i) \ ⋂ i, t i := by
  rw [Set.sdiff_eq, Set.compl_iInter t]; exact Zad6a

theorem Zad6d {s t : ι → Set α} : (⋂ i, s i) ∪ (⋃ i, t i)ᶜ ⊆ ⋂ i, s i ∪ (t i)ᶜ := by
  rw [Set.compl_iUnion]; exact Zad6b

alias Zad8 := Set.iInter_union_of_antitone

theorem Zad9a {s : ι → Set α} {t : ι' → Set β} : (⋃ i, s i) ×ˢ ⋃ j, t j = ⋃ i, ⋃ j, s i ×ˢ t j := by
  ext x; simp

theorem Zad9b [Nonempty ι] [Nonempty ι'] {s : ι → Set α} {t : ι' → Set β} :
    (⋂ i, s i) ×ˢ ⋂ j, t j = ⋂ i, ⋂ j, s i ×ˢ t j := by ext x; simp [forall_and]
