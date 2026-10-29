import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SimpleGraph

@[simps]
def induceInduceIso (G : SimpleGraph V) (s : Set V) (t : Set s) :
    (G.induce s).induce t ≃g G.induce (Subtype.val '' t) where
  toFun v := ⟨v, by simp⟩
  invFun v := ⟨⟨v, by rcases v with ⟨v, h⟩; simp at h; exact h.fst⟩, by
      rcases v with ⟨v, h⟩; simp at h; exact h.snd⟩
  map_rel_iff' := by simp

namespace Walk

variable {G : SimpleGraph V} {P : V → Prop} [DecidablePred P]

/-- The first vertex of a walk that satisfies a predicate, or the end if there isn't one. -/
def firstP (P : V → Prop) [DecidablePred P] {u v} : G.Walk u v → V
| nil => v
| cons _ p => if P u then u else p.firstP P

@[simp] theorem firstP_nil : (nil : G.Walk u u).firstP P = u := (rfl)

@[simp] theorem firstP_cons {h : G.Adj u v} {p : G.Walk v w} :
  (cons h p).firstP P = if P u then u else p.firstP P := (rfl)

theorem firstP_mem_support {p : G.Walk u v} : firstP P p ∈ p.support := by
  induction p with
  | nil => simp
  | cons _ p ih => simp; split <;> simp_all

theorem firstP_of_exists {p : G.Walk u v} (h : ∃ w ∈ p.support, P w) : P (firstP P p) := by
  induction p with
  | nil => simpa using h
  | cons _ p ih => simp_all; split <;> simp_all; exact h.elim (by simpa)

def takeUntilP (P : V → Prop) [DecidablePred P] {u v} : (p : G.Walk u v) → G.Walk u (p.firstP P)
| nil => nil
| cons h p => if hu : P u then nil.copy rfl (by simp [hu]) else
    cons h ((p.takeUntilP P).copy rfl (by simp [hu]))

@[simp] theorem takeUntilP_nil : (nil : G.Walk u u).takeUntilP P = nil.copy rfl (by simp) := (rfl)

@[simp] theorem takeUntilP_cons {h : G.Adj u v} {p : G.Walk v w} : (cons h p).takeUntilP P =
    if hu : P u then nil.copy rfl (by simp [hu]) else
      cons h ((p.takeUntilP P).copy rfl (by simp [hu])) := (rfl)

theorem support_takeUntilP_prefix_support {u v} (p : G.Walk u v) (P : V → Prop) [DecidablePred P] :
    (p.takeUntilP P).support <+: p.support := by
  induction p with
  | nil => simp
  | cons h p ih => simp; split <;> [simp; simpa]

theorem IsPath.takeUntilP (P : V → Prop) [DecidablePred P] {u v} {p : G.Walk u v} (hp : p.IsPath) :
    (p.takeUntilP P).IsPath := mk' ((support_takeUntilP_prefix_support p P).nodup hp.support_nodup)

theorem forall_mem_dropLast_support_takeUntilP_not {p : G.Walk u v} :
    ∀ w ∈ (p.takeUntilP P).support.dropLast, ¬P w := by
  induction p with
  | nil => simp
  | cons h p ih => simp; split <;> [simp; simp_all [List.dropLast_cons_of_ne_nil]]

end Walk

theorem ConnectedComponent.degree_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent)
    (v : C) [Fintype (C.toSimpleGraph.neighborSet v)] [Fintype (G.neighborSet ↑v)] :
    C.toSimpleGraph.degree v = G.degree v := by
  unfold ConnectedComponent.toSimpleGraph SimpleGraph.degree; apply Finset.card_nbij Subtype.val
  · intro w; rw (transparency := .default) [coe_neighborFinset]; simp
  · simp
  · intro w hw; rw (transparency := .default) [coe_neighborFinset]; simp_all
    change w ∈ C.supp; rw [← C.mem_supp_congr_adj hw]; exact v.prop

end SimpleGraph
