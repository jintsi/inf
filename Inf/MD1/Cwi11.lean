import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

theorem List.isChain_scanr {f : α → β → β} (hf : ∀ a b, R (f a b) b) :
    IsChain R (scanr f init as) := by
  induction as with simp
  | cons a as ih => cases as with simp_all

theorem List.isChain_scanl {f : β → α → β} (hf : ∀ b a, R b (f b a)) :
    IsChain R (scanl f init as) := by
  rw [scanl_eq_scanr_reverse, isChain_reverse]
  apply isChain_scanr; simp [flip, hf]

open SimpleGraph Finset

namespace MD1.Cwi11

theorem Zad1 {G : SimpleGraph V} [Nonempty V] : [G.IsTree,
    ∀ (v w : V), ∃! p : G.Walk v w, p.IsPath, Minimal Connected G, Maximal IsAcyclic G].TFAE := by
  rename_i hV
  tfae_have 1 ↔ 2 := by simp only [isTree_iff_existsUnique_path, hV, true_and]
  tfae_have 1 ↔ 3 := isTree_iff_minimal_connected
  tfae_have 1 ↔ 4 := by simp only [isTree_iff_maximal_isAcyclic, hV, true_and]
  tfae_finish

theorem Zad3 {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hG : G.IsTree) :
    G.maxDegree ≤ #{v | G.degree v = 1} := by
  by_cases! Subsingleton V
  · simp
  apply maxDegree_le_of_forall_degree_le; intro w
  let s : Finset V := {v | G.degree v = 1 ∧ v ≠ w}
  suffices G.degree w ≤ #s by
    grw [this]; apply card_le_card; intro w; simp +contextual [s]
  suffices ∑ v ∈ (insert w s)ᶜ, G.degree v + G.degree w + #s + 2 ≤
    ∑ v ∈ (insert w s)ᶜ, G.degree v + #s + #s + 2 by simp_all
  calc ∑ v ∈ (insert w s)ᶜ, G.degree v + G.degree w + #s + 2
  _ = ∑ v ∈ (insert w s)ᶜ, G.degree v + G.degree w + ∑ v ∈ s, G.degree v + 2 := by
    simp [card_eq_sum_ones, -sum_const]; symm; congr! with v hv; simp [s] at hv; exact hv.1
  _ = ∑ v ∈ (insert w s)ᶜ, G.degree v + ∑ v ∈ insert w s, G.degree v + 2 := by
    rw [sum_insert, ← add_assoc]; simp [s]
  _ = 2 * Fintype.card V := by
    rw [sum_compl_add_sum, sum_degrees_eq_twice_card_edges, ← hG.card_edgeFinset, mul_add]
  _ = 2 * #(insert w s)ᶜ + 2 * #(insert w s) := by rw [← mul_add, card_compl_add_card]
  _ = #(insert w s)ᶜ • 2 + #s + #s + 2 := by
    rw [card_insert_of_notMem]; simp [mul_add, mul_comm, two_mul, add_assoc]; simp [s]
  _ ≤ ∑ v ∈ (insert w s)ᶜ, G.degree v + #s + #s + 2 := by
    simp only [add_le_add_iff_right]; apply card_nsmul_le_sum; simp [s]
    intro x; have := hG.preconnected.degree_pos_of_nontrivial x; lia

end MD1.Cwi11

/-- The hypercube graph with dimensions indexed by `d`. -/
@[simps]
def SimpleGraph.hypercubeGraph (d : Type*) [DecidableEq d] : SimpleGraph (d → Fin 2) where
  Adj v w := ∃ i, w = v + Pi.single i 1
  symm.symm v w := by rintro ⟨i, rfl⟩; use i; simp [add_assoc, ← Pi.single_add]

instance [Fintype d] [DecidableEq d] : DecidableRel (hypercubeGraph d).Adj :=
  inferInstanceAs (DecidableRel fun v w => ∃ i, w = v + Pi.single i 1)

@[simp]
theorem SimpleGraph.hypercubeGraph_degree [Fintype d] [DecidableEq d] (v : d → Fin 2) :
    (hypercubeGraph d).degree v = Fintype.card d := by
  simp [← card_neighborFinset_eq_degree, neighborFinset]
  calc #{w | ∃ i, w = v + Pi.single i 1}
  _ = #(univ.image fun i => v + Pi.single i 1) := by congr; ext w; simp [eq_comm]
  _ = Fintype.card d := by
    rw [card_image_of_injective, card_univ]; simp [Function.Injective]
    intro i j h; simp [funext_iff] at h; specialize h i; simp_all [Pi.single, Function.update]

/-- The shortest path between two vertices on a hypercube. -/
noncomputable def SimpleGraph.hypercube_path [Fintype d] [DecidableEq d] (u v : d → Fin 2) :
    (hypercubeGraph d).Walk u v := by
  refine (Walk.ofSupport ((Finset.toList {i | u i ≠ v i}).scanl (fun v i => v + Pi.single i 1) u)
    (by simp) (List.isChain_scanl fun v i => by use i)).copy (by simp) ?_
  simp [List.getLast_scanl]
  calc (Finset.toList {i | u i ≠ v i}).foldl (fun v i => v + Pi.single i 1) u
  _ = ((Finset.toList {i | u i ≠ v i}).map fun i => Pi.single i 1).foldl (fun v i => v + i) u := by
    simp [List.foldl_map]
  _ = u + ((Finset.toList {i | u i ≠ v i}).map fun i => Pi.single i 1).foldl (fun v i => v + i) 0 := by
    convert List.foldl_assoc; simp; infer_instance
  _ = u + ((Finset.toList {i | u i ≠ v i}).map fun i => Pi.single i 1).sum := by rw [List.sum_eq_foldl]
  _ = u + ∑ i ∈ {i | u i ≠ v i}, Pi.single i 1 := by simp
  _ = v := by ext1 i; simp; generalize u i = x; generalize v i = y; fin_cases x <;> fin_cases y <;> simp

theorem SimpleGraph.hypercube_dist [Fintype d] [DecidableEq d] (u v : d → Fin 2) :
    (hypercubeGraph d).dist u v = #{i | u i ≠ v i} := by
  rw [dist_eq_sInf, csInf_eq_iff] <;> simp [Set.range_nonempty_iff_nonempty] <;> use! hypercube_path u v
  · simp [hypercube_path]
  intro p; induction p with simp
  | @cons u v w h p ih =>
    symm at h; simp at h; rcases h with ⟨i, rfl⟩; simp
    calc #{x | v x + _ ≠ w x}
    _ ≤ #(insert i ({x | v x ≠ w x} : Finset d)) := by
      gcongr; intro x; simp; contrapose!; simp +contextual
    _ ≤ p.length + 1 := by grw [card_insert_le, ih]

namespace MD1.Cwi11

theorem Zad5i [Fintype d] [DecidableEq d] :
    2 * #(hypercubeGraph d).edgeFinset = 2 ^ Fintype.card d * Fintype.card d := by
  simp [← sum_degrees_eq_twice_card_edges]

theorem Zad5ii [Fintype d] [DecidableEq d] : (hypercubeGraph d).diam = Fintype.card d := by
  rw [diam_def]; trans ENat.toNat (⨆ p : _ × _, (hypercubeGraph d).dist p.1 p.2)
  · congr! with ⟨u, v⟩; rw [Reachable.coe_dist_eq_edist]; use hypercube_path u v
  have hb : BddAbove (Set.range fun p : _ × _ => (hypercubeGraph d).dist p.1 p.2) := by
    use Fintype.card d; simp [upperBounds]; intro _ u v rfl; simp [hypercube_dist, card_le_univ]
  rw [← ENat.coe_iSup hb, ENat.toNat_coe]; apply le_antisymm
  · apply ciSup_le; simp [hypercube_dist, card_le_univ]
  · apply le_ciSup_of_le hb (0, 1); simp [hypercube_dist]

theorem Zad5iii [Nontrivial d] [DecidableEq d] : (hypercubeGraph d).girth = 4 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne d
  let w := Walk.nil' (G := hypercubeGraph d) 0
    |>.cons (u := Pi.single i 1) (by symm; use i; rw [zero_add])
    |>.cons (u := Pi.single i 1 + Pi.single j 1) (by symm; use j)
    |>.cons (u := Pi.single j 1) (by use i; rw [add_comm])
    |>.cons (u := 0) (by use j; rw [zero_add])
  have hw : w.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]; and_intros; swap
    · simp [w]
    simp [w]; simp [funext_iff]; use! i, (by simp [hij]), j, by simp [hij]
  suffices (hypercubeGraph d).girth ≠ 3 by
    have := girth_le_length hw; simp [w] at this
    have := (hypercubeGraph d).three_le_girth (by simp [IsAcyclic]; exists 0, w)
    lia
  suffices ∀ v (p : (hypercubeGraph d).Walk v v), p.IsCycle → p.length ≠ 3 by
    contrapose! this; simp_rw [eq_comm, ← this, exists_girth_eq_length]
    simp [IsAcyclic]; exists 0, w
  intro v p h; contrapose! h; exfalso; match p, h with
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    simp_all; rename_i u w
    rcases h1 with ⟨i1, rfl⟩; rcases h2 with ⟨i2, rfl⟩; rcases h3 with ⟨i3, h⟩
    revert h; simp [funext_iff]
    by_cases! h12 : i1 = i2
    · subst h12; use i3; rw [add_assoc (v i3)]
      conv => arg 1; rhs; lhs; rhs; rw [← Pi.add_apply, ← Pi.single_add]
      simp
    by_cases! h13 : i1 = i3
    · subst h13; use i2; rw [add_right_comm, add_assoc (v i2)]
      conv => arg 1; rhs; lhs; rhs; rw [← Pi.add_apply, ← Pi.single_add]
      simp
    use i1; simp [h12, h13]

alias Zad6i := radius_le_ediam
alias Zad6ii := ediam_le_two_mul_radius

alias Zad7 := connected_or_connected_compl
