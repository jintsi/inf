import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Inf.MD2.SimpleGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
--import Mathlib.Combinatorics.SimpleGraph.DegreeSum

theorem List.IsPrefix.tail {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₁.tail <+: l₂.tail := by
  rcases l₁ with (_ | ⟨a₁, l₁⟩); · simp
  rcases l₂ with (_ | ⟨a₂, l₂⟩); · simp at h
  simp_all

@[simp]
theorem finsum_one' : ∑ᶠ _ : α, 1 = Nat.card α := by
  rw [← Set.ncard_univ, ← finsum_one]; simp

namespace MD2.Cwi1

open SimpleGraph

theorem Zad1 [Finite V] {G : SimpleGraph V} (hG : G.Connected) {n : ℕ} (hV : n < Nat.card V) :
    ∃ s : Finset V, s.card = n ∧ (G.induce sᶜ).Connected := by
  induction n generalizing V with
  | zero =>
    use ∅; simp; rw [Finset.coe_empty, Set.compl_empty]; rwa [(induceUnivIso G).connected_iff]
  | succ n ih =>
    have : Nontrivial V := by rw [← Finite.one_lt_card_iff_nontrivial]; omega
    let ⟨v, hv⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let ⟨s, hs, hsv⟩ := ih hv (by simp; omega)
    use (s.map (Function.Embedding.subtype _)).cons v (by simp), by simpa
    rw [(G.induceInduceIso _ _).connected_iff] at hsv
    convert hsv; all_goals ext; simp; tauto

theorem Zad2 {G : SimpleGraph V} (hG : G.Connected) {k : ℕ}
    (hmax : ∀ u v, ∀ p : G.Walk u v, p.IsPath → p.length ≤ k) {p : G.Walk u v} (hp : p.IsPath)
    {q : G.Walk u' v'} (hq : q.IsPath) (hlp : p.length = k) (hlq : q.length = k) :
    ∃ w, w ∈ p.support ∧ w ∈ q.support := by
  contrapose! hmax with hdisj
  suffices ∃ w ∈ p.support, ∃ w' ∈ q.support, ∃ r : G.Walk w w', r.IsPath ∧
    r.support.tail.Disjoint p.support ∧ r.support.dropLast.Disjoint q.support by
    rcases this with ⟨w, hw, w', hw', r, hr, h, h'⟩
    have hlr : 0 < r.length := by simp [Nat.pos_iff_ne_zero]; rintro ⟨_⟩; exact hdisj _ hw hw'
    simp [Walk.mem_support_iff_exists_append] at hw hw'
    rcases hw with ⟨p₁, p₂, rfl⟩; rcases hw' with ⟨q₁, q₂, rfl⟩; rw [Walk.length_append] at hlp hlq
    rcases le_total p₂.length p₁.length with (hp' | hp')
    · use u; let P := p₁.append r; have hP : P.IsPath := by
        rw [Walk.isPath_append] at ⊢ hp; use hp.1, hr.tail
        simp [Walk.support_append] at h; symm; simp [h]
      rcases le_total q₂.length q₁.length with (hq' | hq')
      · use u', P.append q₁.reverse; and_intros; swap; · simp [P]; omega
        rw [Walk.isPath_append']; use hP.dropLast, hq.of_append_left.reverse
        unfold P; simp [Walk.support_append_eq_support_dropLast_append]; and_intros
        · intro x hx; simp at hdisj; exact (hdisj x (Or.inl (List.mem_of_mem_dropLast hx))).1
        · simp [Walk.support_append] at h'; simp [h']
      · use v', P.append q₂; and_intros; swap; simp [P]; omega
        rw [Walk.isPath_append']; use hP.dropLast, hq.of_append_right
        unfold P; simp [Walk.support_append_eq_support_dropLast_append]; and_intros
        · intro x hx; simp at hdisj; exact (hdisj x (Or.inl (List.mem_of_mem_dropLast hx))).2
        · simp [Walk.support_append_eq_support_dropLast_append] at h'; simp [h']
    · use v; let P := p₂.reverse.append r; have hP : P.IsPath := by
        rw [Walk.isPath_append]; rw [Walk.isPath_append'] at hp; use hp.2.1.reverse, hr.tail
        simp [Walk.support_append_eq_support_dropLast_append] at h; symm; simp [h]
      rcases le_total q₂.length q₁.length with (hq' | hq')
      · use u', P.append q₁.reverse; and_intros; swap; · simp [P]; omega
        rw [Walk.isPath_append']; use hP.dropLast, hq.of_append_left.reverse
        unfold P; simp [Walk.support_append_eq_support_dropLast_append]; and_intros
        · intro x hx; simp at hdisj; exact (hdisj x (Or.inr (List.mem_of_mem_tail hx))).1
        · simp [Walk.support_append] at h'; simp [h']
      · use v', P.append q₂; and_intros; swap; simp [P]; omega
        rw [Walk.isPath_append']; use hP.dropLast, hq.of_append_right
        unfold P; simp [Walk.support_append_eq_support_dropLast_append]; and_intros
        · intro x hx; simp at hdisj; exact (hdisj x (Or.inr (List.mem_of_mem_tail hx))).2
        · simp [Walk.support_append_eq_support_dropLast_append] at h'; simp [h']
  let ⟨r₀, hr₀⟩ := hG.exists_isPath u u'
  classical
  let r₁ := r₀.takeUntilP (· ∈ q.support)
  let r := (r₁.reverse.takeUntilP (· ∈ p.support)).reverse
  exists _, (by apply Walk.firstP_of_exists; use u; simp), _,
    (by apply Walk.firstP_of_exists; use u'; simp), r; and_intros
  · unfold r r₁; simp; apply Walk.IsPath.takeUntilP; simp; apply Walk.IsPath.takeUntilP; exact hr₀
  · unfold r; simp [List.Disjoint]; apply Walk.forall_mem_dropLast_support_takeUntilP_not
  · unfold r r₁; simp; intro w hw; apply (Walk.support_takeUntilP_prefix_support ..).tail.mem at hw
    revert hw; simp; apply Walk.forall_mem_dropLast_support_takeUntilP_not

theorem Zad3 {G : SimpleGraph V} :
    Nat.card V ≤ Set.ncard G.edgeSet + Nat.card G.ConnectedComponent := by
  cases finite_or_infinite V; swap; · simp
  rw [← Set.ncard_univ, ← G.iUnion_connectedComponentSupp, Set.ncard_iUnion_of_finite]
  case hs => unfold Set.Finite; infer_instance
  case h => intro C D; contrapose; simp [Function.onFun, Set.not_disjoint_iff]; intro x rfl; simp
  have := Fintype.ofFinite V
  classical rw [finsum_eq_sum_of_fintype, ← G.sum_connectedComponent_ncard_edgeSet,
    Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones, ← Finset.sum_add_distrib]
  gcongr with c; exact c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one

/-- Todo: simpler proof once i prove that an Eulerian circuit exists -/
theorem Zad4 [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hv : ∀ v, Even (G.degree v)) : ∀ e ∈ G.edgeSet, ¬G.IsBridge e := by
  have h := hv
  intro e he; contrapose h; simp_rw [not_forall, Nat.not_even_iff_odd]
  cases e with | h u v
  let G' := ((G.deleteEdges {s(u, v)}).connectedComponentMk v).toSimpleGraph
  classical have ⟨w, hwv, hw⟩ := G'.exists_ne_odd_degree_of_exists_odd_degree ⟨v,
    ConnectedComponent.connectedComponentMk_mem⟩ (by
      unfold G'; rw [ConnectedComponent.degree_toSimpleGraph]
      specialize hv v; rw [← card_neighborFinset_eq_degree] at ⊢ hv
      simp [deleteEdges]; rw (transparency := .default) [neighborFinset_sdiff]
      convert_to Odd (G.neighborFinset v \ {u}).card
      · congr; ext w; simp; constructor; · tauto
        intro rfl; constructor; · right; rfl
        apply Ne.symm; simpa using G.not_isDiag_of_mem_edgeSet he
      · rwa [Finset.sdiff_singleton_eq_erase, ← Nat.not_even_iff_odd, ← Nat.even_add_one,
          Finset.card_erase_add_one]; simp; symm; simpa using he)
  use w; unfold G' at hw; rw [ConnectedComponent.degree_toSimpleGraph] at hw
  convert hw using 1; rw [degree, degree]; congr 1; ext x; simp; intro hx; constructor; swap
  · intro hv rfl; apply hwv; ext; simpa
  clear hw; rcases w with ⟨w, hw⟩; simp_all; rintro rfl -
  have := ConnectedComponent.reachable_of_mem_supp (v := v) _ hw rfl
  exact isBridge_iff.mp h this

/-
theorem Zad5 [Fintype V] {G : SimpleGraph V} [G.LocallyFinite] (hb : G.IsBipartite)
    {d : ℕ} (hn : 2 ≤ d) (hr : G.IsRegularOfDegree d) : ∀ e ∈ G.edgeSet, ¬G.IsBridge e := by
  intro e he h; cases e with | h u v
  let G' := ((G.deleteEdges {s(u, v)}).connectedComponentMk v).toSimpleGraph
  apply IsBipartite.exists_isBipartiteWith at hb; rcases hb with ⟨s, t, hb⟩
  have hb' : G'.IsBipartite := by
-/
