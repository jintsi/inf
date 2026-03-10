import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Peel

/-- Pigeonhole principle, halfway between `Fintype.exists_ne_map_eq_of_card_lt` and
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` -/
theorem Fintype.exists_ne_map_eq_of_card_lt_of_maps_to [Fintype α] {s : Finset β}
    (hc : s.card < card α) {f : α → β} (hf : ∀ x, f x ∈ s) : ∃ x y, x ≠ y ∧ f x = f y := by
  convert Finset.univ.exists_ne_map_eq_of_card_lt_of_maps_to hc ?hf <;> try simp; trivial

/-- Pigeonhole principle, halfway between `Fintype.exists_le_card_fiber_of_mul_le_card`
and `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to` -/
theorem Fintype.exists_le_card_fiber_of_mul_le_card_of_maps_to [Fintype α] [DecidableEq β]
    {s : Finset β} {f : α → β} {n : ℕ} (hf : ∀ x, f x ∈ s) (hs : s.Nonempty)
    (hn : s.card * n ≤ card α) : ∃ y ∈ s, n ≤ Finset.card {x | f x = y} := by
  convert Finset.univ.exists_le_card_fiber_of_mul_le_card_of_maps_to ?hf hs hn; simpa

/-- Pigeonhole principle, halfway between `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to`
and `Fintype.exists_le_card_fiber_of_mul_le_card` -/
theorem Finset.exists_le_card_fiber_of_mul_le_card {α β : Type*} [DecidableEq β] [Fintype β]
    {s : Finset α} (f : α → β) {n : ℕ} [Nonempty β] (hn : Fintype.card β * n ≤ s.card) :
    ∃ y, n ≤ card {x ∈ s | f x = y} := by
  convert s.exists_le_card_fiber_of_mul_le_card_of_maps_to ?hf Finset.univ_nonempty hn
    <;> try simp <;> trivial

namespace MD1.Cwi1

theorem Zad2i (n : ℕ) : ∑ k ∈ Finset.range (n + 1), Nat.fib k = Nat.fib (n + 2) - 1 := by
  rw [Nat.fib_succ_eq_succ_sum]; rfl

theorem Zad2ii (n : ℕ) : 5 ∣ Nat.fib (5 * n) := by
  induction n
  · simp
  · grind [Nat.fib_add_two]

theorem Zad2iii (n : ℕ) : Nat.fib n < 2 ^ n := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  cases n; simp
  rename_i n; cases n; simp
  grind [Nat.fib_add_two]

end MD1.Cwi1

-- TODO: tournaments

theorem SimpleGraph.mem_universalVerts_iff_card (G : SimpleGraph V) (v : V) [Fintype V]
    [DecidableRel G.Adj] [DecidableEq V] : v ∈ G.universalVerts ↔ G.degree v = Fintype.card V - 1 := by
  rw [← (Nat.le_sub_one_of_lt (G.degree_lt_card_verts v)).ge_iff_eq, ← Nat.sub_eq_zero_iff_le,
    ← degree_compl, degree_eq_zero_iff_notMem_support, mem_support]
  simp [universalVerts, adj_comm];

namespace MD1.Cwi1

theorem Zad6 (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [DecidableEq V] [Nontrivial V] :
    ∃ x y, x ≠ y ∧ G.degree x = G.degree y := by
  by_cases hmax : G.maxDegree = Fintype.card V - 1
  · have ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    symm at hv
    simp [hmax, ← G.mem_universalVerts_iff_card, SimpleGraph.universalVerts] at hv
    have hmin : 1 ≤ G.minDegree := by
      apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro w; apply Nat.one_le_of_lt (a := 0); by_cases h : v = w
      · subst h; have ⟨w, h⟩ := exists_ne v
        exact (hv h.symm).degree_pos_right
      · exact (hv h).degree_pos_left
    apply Fintype.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.Icc 1 (G.maxDegree))
    · simp; exact G.maxDegree_lt_card_verts
    · simp [G.degree_le_maxDegree]; exact fun w => hmin.trans (G.minDegree_le_degree w)
  apply Fintype.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (Fintype.card V - 1))
  · simp; exact Fintype.card_pos
  · simp; intro; grw [G.degree_le_maxDegree]; grind [G.maxDegree_lt_card_verts]

theorem Zad7 {n : ℕ} [NeZero n] (f : Equiv.Perm (Fin n)) (h : ∀ x, f x ≠ x) :
    ∃ i x y, x ≠ y ∧ f x + i = x ∧ f y + i = y := by
  rsuffices ⟨x, y, hne, h⟩ : ∃ x y, x ≠ y ∧ x - f x = y - f y
  · exists x - f x, x, y, hne; simp; simp [h]
  apply Fintype.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.Ioi 0)
  · simp [NeZero.pos]
  · intro x; simp [Fin.pos_iff_ne_zero, sub_eq_zero]; exact (h x).symm

theorem Zad8 {n : ℕ} [NeZero n] (f : Fin n → ℤ) :
    ∃ a b, a ≤ b ∧ (n : ℤ) ∣ ∑ i ∈ Finset.Icc a b, f i := by
  simp [Int.dvd_iff_emod_eq_zero]
  by_cases! h : ∃ x, (∑ i ∈ Finset.Icc 0 x, f i) % n = 0
  · exists 0; simp [h]
  · have ⟨x, y, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.Ioo 0 (n : ℤ)) (f := fun x => (∑ i ∈ Finset.Icc 0 x, f i) % n) ?_ ?_
    · wlog! hxy : x < y generalizing x y
      · exact this y x hne.symm h.symm (hne.lt_of_le' hxy)
      have : x + 1 ≤ y := by
        rw! (castMode := .all) [show n = n - 1 + 1 by lia]
        apply Fin.add_one_le_of_lt; convert hxy <;> lia
      exists x + 1, y, this
      rw [Fin.Icc_add_one_eq_Ioc (by lia), show Finset.Ioc x y = Finset.Icc 0 y \ Finset.Icc 0 x by
          rw [← Finset.coe_inj]; simp [Set.ext_iff, and_comm],
        Finset.sum_sdiff_eq_sub (Finset.Icc_subset_Icc_right hxy.le), Int.sub_emod, h, sub_self]; rfl
    · simp [NeZero.pos]
    · simp [Int.emod_lt_of_pos, NeZero.pos]; peel h
      exact this.lt_of_le' (Int.emod_nonneg _ (NeZero.ne _))

theorem Zad9 [Nonempty α] [Fintype α] {F : Set (Set α)}
    (h : F.ncard > Fintype.card (Set α) / 2) : ∃ s ∈ F, ∃ t ∈ F, s ⊆ t := by
  have ⟨a⟩ := ‹Nonempty α›
  have ⟨s, hs, t, ht, hne, h⟩ := F.exists_ne_map_eq_of_ncard_lt_of_maps_to ?_ ?_
      (f := fun x => x \ {a}) (t := (Set.univ \ {a}).powerset)
  · have : (a ∈ s ∧ a ∉ t) ∨ (a ∉ s ∧ a ∈ t) := by
      by_contra!; by_cases ha : a ∈ s; apply_fun insert a at h
      all_goals simp [ha, this] at h; exact hne h
    cases this with
    | inl ha => simp [ha] at h; subst h; exact ⟨s \ {a}, ht, s, hs, Set.diff_subset⟩
    | inr ha => simp [ha] at h; subst h; exact ⟨t \ {a}, hs, t, ht, Set.diff_subset⟩
  · simp [Nat.pow_sub_one] at ⊢ h; assumption
  · simp

theorem Zad10 [Nonempty X] [Fintype X] [DecidableEq X] {F : Finset (Finset X)}
    (h : ∀ s ∈ F, Fintype.card X ≤ s.card * 2) : ∃ x, F.card ≤ {s ∈ F | x ∈ s}.card * 2 := by
  let F' : Finset _ := {(s, x) : Finset X × X | s ∈ F ∧ x ∈ s}
  have hF' : F.card * Fintype.card X ≤ F'.card * 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (by simp [Set.MapsTo, F']; tauto)]
    simp [F', Finset.filter_filter]
    calc F.card * Fintype.card X
      _ = ∑ x ∈ F, Fintype.card X := (Finset.sum_const_nat fun _ _ => rfl).symm
      _ ≤ ∑ x ∈ F, x.card * 2 := Finset.sum_le_sum h
      _ = (∑ x ∈ F, x.card) * 2 := (Finset.sum_mul _ _ _).symm
      _ = (∑ x ∈ F, Finset.card {a : Finset X × X | (a.1 ∈ F ∧ a.2 ∈ a.1) ∧ a.1 = x}) * 2 := by
        simp; apply Finset.sum_congr rfl; intro x hx; apply Finset.card_nbij fun i => (x, i)
          <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def]
          <;> (intros; subst_vars; trivial)
  -- kinda hacky way to get the * 2 through the pigeonhole,
  -- should have probably used the weighted version
  have ⟨x, h⟩ := (F' ×ˢ (.univ : Finset Bool)).exists_le_card_fiber_of_mul_le_card
    (fun x => x.1.2) (n := F.card) (by simp; rwa [mul_comm])
  exists x; convert h
  simp [Finset.filter_product_left fun x' : Finset X × X => x'.2 = x, F', Finset.filter_filter]
  apply Finset.card_nbij fun s => (s, x) <;> simp [Set.MapsTo, Set.SurjOn, Set.subset_def]
  intros; subst_vars; trivial
