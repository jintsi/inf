import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Nat.Choose.Vandermonde

namespace MD1.Cwi2

open Finset

set_option backward.isDefEq.respectTransparency.types false
theorem Zad1 : #{s : Finset (Fin n × Fin n) | #s = n ∧ Set.Pairwise (s : Set (Fin n × Fin n))
    fun x y => x.1 ≠ y.1 ∧ x.2 ≠ y.2} = n.factorial := by
  trans Fintype.card (Equiv.Perm (Fin n)); swap; simp [Fintype.card_perm]
  apply card_eq_of_equiv_fintype; constructor
  case toFun =>
    rintro ⟨s, hs⟩; simp at hs
    have row : s ≃ Fin n := Equiv.ofBijective (fun r => r.val.fst) (by
      rw [Fintype.bijective_iff_injective_and_card]; simp [hs.1]
      intro x y h; contrapose h; exact (hs.2 x.property y.property (by simpa using h)).1)
    have col : s ≃ Fin n := Equiv.ofBijective (fun r => r.val.snd) (by
      rw [Fintype.bijective_iff_injective_and_card]; simp [hs.1]
      intro x y h; contrapose h; exact (hs.2 x.property y.property (by simpa using h)).2)
    exact row.symm.trans col
  case invFun =>
    intro p; use univ.map ⟨fun i => (i, p i), fun x y => by simp⟩; simp [Set.Pairwise]
  case left_inv =>
    rintro ⟨s, hs⟩; simp [map_eq_image]; rw [image_eq_iff_surjOn_mapsTo, and_iff_right_of_imp]
    · simp; intro x; generalize h : Equiv.ofBijective _ _ = e; convert (e.symm x).property
      rw [← h]; symm; apply Equiv.ofBijective_apply_symm_apply (fun r : s => r.val.fst)
    · intro hf; apply surjOn_of_injOn_of_card_le
      · exact hf
      · simp; intro i j; simp; tauto
      · simp at hs; simp [hs.1]
  case right_inv =>
    intro p; simp; rw [← Equiv.coe_inj, Equiv.coe_trans, Equiv.comp_symm_eq]; simp [funext_iff]

/-
set_option backward.isDefEq.respectTransparency.types false
theorem Zad2 [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    #{s : Finset (α × β) | #s = k ∧ Set.Pairwise (s : Set (α × β)) fun x y => x.1 ≠ y.1 ∧ x.2 ≠ y.2}
    = (Fintype.card α).choose k * (Fintype.card β).choose k * k.factorial := by
  trans #(powersetCard k (univ : Finset α) ×ˢ powersetCard k (univ : Finset β) ×ˢ
    ({s : Finset (Fin k × Fin k) | #s = k ∧
      Set.Pairwise (s : Set (Fin k × Fin k)) fun x y => x.1 ≠ y.1 ∧ x.2 ≠ y.2} : Finset _))
  swap; simp [Zad1, mul_assoc]; apply card_bij'
  case i =>
    intro s hs; use s.image Prod.fst, s.image Prod.snd; simp at hs
    have ea : (s.image Prod.fst) ≃ Fin k := equivFinOfCardEq ((card_image_of_injOn fun x hx y hy =>
      Function.mtr fun h => (hs.2 hx hy h).1).trans hs.1)
    have eb : (s.image Prod.snd) ≃ Fin k := equivFinOfCardEq ((card_image_of_injOn fun x hx y hy =>
      Function.mtr fun h => (hs.2 hx hy h).2).trans hs.1)
    exact s.attach.image fun r => (Equiv.Finset.prod _ _).trans (ea.prodCongr eb) ⟨r.val, by
      simp [← exists_and_right, ← exists_and_left]; use r.val.1, r.val.2; simp⟩
  case hi =>
    intro s hs; generalize_proofs ha hb; simp at hs; simp [*]; and_intros
    · rw [card_image_of_injOn, card_attach, hs.1]; intro x hx y hy; simp [Equiv.Finset.prod, ← Prod.ext_iff]
    · apply Pairwise.range_pairwise; simp [Pairwise, Equiv.Finset.prod, -Prod.mk.injEq, Function.onFun]
      intro _ _ hx _ _ hy; exact hs.2 hx hy
  case j =>
    intro (a, b, s) h; simp at h
    have ea := equivFinOfCardEq h.1; have eb := equivFinOfCardEq h.2.1
    exact s.map (((Equiv.Finset.prod _ _).trans (ea.prodCongr eb)).symm.toEmbedding.trans
      (Function.Embedding.subtype _))
  case hj =>
    intro (a, b, s) h; simp at h; simp [h.2.2.1, Set.Pairwise, -Prod.forall, Equiv.Finset.prod]
    rintro _ _ _ hx rfl _ _ _ hy rfl; convert h.2.2.2 hx hy <;> simp
  case left_inv =>
    intro s hs; simp [map_eq_image, image_image]
    convert attach_image_val; simp [funext_iff, Equiv.Finset.prod]; infer_instance
  case right_inv =>
    simp; intro a b s ha hb hs H; rw [and_iff_left_of_imp]
    · ext i; simp [Equiv.Finset.prod]; constructor
      · rintro ⟨i, _, rfl⟩; simp
      · intro hi; use equivFinOfCardEq ha ⟨i, hi⟩; simp
        suffices Set.SurjOn Prod.fst (s : Set (Fin k × Fin k)) Set.univ by simpa using this trivial
        rw [← coe_univ]; apply surjOn_of_injOn_of_card_le; simp; swap; simp [hs]
        intro x hx y hy h; contrapose h; exact (H hx hy h).1
    intro ha'; rw [and_iff_left_of_imp]
    · ext j; simp [Equiv.Finset.prod]; constructor
      · rintro ⟨_, j, _, rfl⟩; simp
      · intro hj; rw [exists_comm]; use equivFinOfCardEq hb ⟨j, hj⟩; simp
        suffices Set.SurjOn Prod.snd (s : Set (Fin k × Fin k)) Set.univ by simpa using this trivial
        rw [← coe_univ]; apply surjOn_of_injOn_of_card_le; simp; swap; simp [hs]
        intro x hx y hy h; contrapose h; exact (H hx hy h).2
    intro hb'; ext ⟨ri, rj⟩; simp [Equiv.Finset.prod]; generalize_proofs; constructor
    · simp; rintro _ _ i j hij rfl rfl hr; generalize_proofs at hr; admit
    · intro hr; use! (equivFinOfCardEq ha).symm ri, (equivFinOfCardEq hb).symm rj, ri, rj
      admit
-/

theorem Zad3i : #{f : Fin n → Bool | (List.ofFn f).IsChain fun a b => a = false ∨ b = false}
    = (n + 2).fib := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Nat.fib]
  | more n ih ih' =>
    let p n (f : Fin n → Bool) := (List.ofFn f).IsChain fun a b => a = false ∨ b = false
    calc #{f | p (n + 2) f}
    _ = #{f | p (n + 2) f ∧ f 0 = true} + #{f | p (n + 2) f ∧ f 0 = false} := by
      symm; rw [← Finset.filter_filter, ← Finset.filter_filter]
      convert card_filter_add_card_filter_not _; simp; infer_instance
    _ = #{f | p n f} + #{f | p (n + 1) f} := by
      congr 1 <;> apply (newGoals := .all) card_nbij'
      · exact fun f => Fin.tail (Fin.tail f)
      · exact fun f => Fin.cons true (Fin.cons false f)
      · simp [Set.MapsTo, p, Fin.tail_def]; intro _ _ h _; exact h.of_cons
      · simp [Set.MapsTo, p]; intro _ h; exact h.cons (by simp)
      · simp [Set.LeftInvOn, p, funext_iff]; intro f hf1 h hf0 i; cases i using Fin.cases with
        | zero => simpa
        | succ i => cases i using Fin.cases with
          | zero => simpa [hf0] using hf1.resolve_left
          | succ i => rfl
      · simp [Set.RightInvOn, Set.LeftInvOn]
      · exact Fin.tail
      · exact Fin.cons (α := fun _ => Bool) false
      · simp [Set.MapsTo, p]; tauto
      · simp [Set.MapsTo, p]
      · simp [Set.LeftInvOn, funext_iff]; intro f _ hf0 i; cases i using Fin.cases with
        | zero => simpa
        | succ i => rfl
      · simp [Set.RightInvOn, Set.LeftInvOn]
    _ = (n + 2 + 2).fib := by rw [ih, ih', ← Nat.fib_add_two]

end MD1.Cwi2

theorem composition_length_card (n k : ℕ) [NeZero n] :
    Finset.card {c : Composition n | c.length = k + 1} = (n - 1).choose k :=
  calc Finset.card {c : Composition n | c.length = k + 1}
  _ = Finset.card {c : CompositionAsSet n | c.length = k + 1} :=
    Finset.card_equiv (compositionEquiv n) fun c => by simp [compositionEquiv]
  _ = Finset.card {s : Finset (Fin (n - 1)) | s.card = k} :=
    (Finset.card_equiv (compositionAsSetEquiv n).symm fun s => by
      simp [compositionAsSetEquiv, CompositionAsSet.length, ← Finset.filter_union_right]
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
        <;> simp [Finset.filter_eq', add_comm 1, NeZero.ne]
      · apply Eq.congr_left
        apply Finset.card_nbij (fun i => (i.castSucc.cast (Nat.sub_one_add_one (NeZero.ne n))).succ)
          <;> simp [Set.MapsTo, Set.SurjOn, Set.subset_def]
        · exact fun x hx => ⟨x, hx, rfl⟩
        · intro x y hy hx; exists y, hy; rw [← Fin.val_inj]; simp [hx.symm]
      · intro x hx; grind
    ).symm
  _ = (n - 1).choose k := by simp

theorem FinVec.composition_pos_card (n k : ℕ) [NeZero n] [NeZero k] :
    {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n}.ncard = (n - 1).choose (k - 1) :=
  calc {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n}.ncard
  _ = {c : Composition n | c.length = k}.ncard := by
    apply Set.ncard_congr fun x hx => {
      blocks := List.ofFn x, blocks_pos := by simp [hx.left]
      blocks_sum := by simp_all [List.sum_ofFn]} <;> simp [Composition.length, Composition.ext_iff]
    intro c hc; use fun i => c.blocksFun (i.cast hc.symm)
    simp [Composition.blocksFun, -List.get_eq_getElem, Fin.sum_congr']; constructor; simp
    conv => rhs; rw [← Composition.ofFn_blocksFun]
    rw [List.ofFn_inj', Fin.sigma_eq_iff_eq_comp_cast]; use hc.symm
    ext x; simp [Composition.blocksFun]
  _ = Finset.card {c : Composition n | c.length = k} := by convert Set.ncard_coe_finset _; simp
  _ = (n - 1).choose (k - 1) := by
    convert composition_length_card n (k - 1); exact (Nat.sub_add_cancel NeZero.one_le).symm

theorem FinVec.composition_card (n k : ℕ) [NeZero k] :
    {x : Fin k → ℕ | FinVec.sum x = n}.ncard = (n + k - 1).choose (k - 1) :=
  calc {x : Fin k → ℕ | FinVec.sum x = n}.ncard
  _ = {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n + k}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun x i => x i + 1)
    simp [Set.BijOn, Set.MapsTo, ← Finset.sum_add_card_nsmul, Set.InjOn, funext_iff,
      Set.SurjOn, Set.subset_def]; intro x hpos hsum; use fun i => x i - 1; and_intros
    · conv at hsum => lhs; rhs; ext i; rw [← Nat.sub_add_cancel (hpos i)]
      rw [← Finset.sum_add_card_nsmul] at hsum; simp_all
    · simp; exact fun i => Nat.sub_add_cancel (hpos i)
  _ = (n + k - 1).choose (k - 1) := FinVec.composition_pos_card (n + k) k

namespace MD1.Cwi2

open Finset

theorem Zad4i : {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | x₁ + x₂ + x₃ + x₄ = 7}.ncard = 120 :=
  calc {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | x₁ + x₂ + x₃ + x₄ = 7}.ncard
  _ = {x : Fin 4 → ℕ | FinVec.sum x = 7}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun ⟨x, y, z, w⟩ => ![x, y, z, w])
    simp [Set.BijOn, Set.MapsTo, FinVec.sum, Set.SurjOn, Set.subset_def]
    exact fun x hx => ⟨x 0, x 1, x 2, x 3, hx, FinVec.etaExpand_eq x⟩
  _ = Nat.choose 10 3 := FinVec.composition_card _ _

theorem Zad4ii : {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | 0 < x₁ ∧ 0 < x₂ ∧ 0 < x₃ ∧ 0 < x₄
    ∧ x₁ + x₂ + x₃ + x₄ = 7}.ncard = 20 :=
  calc {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | _}.ncard
  _ = {x : Fin 4 → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = 7}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun ⟨x, y, z, w⟩ => ![x, y, z, w])
    simp [Set.BijOn, Set.MapsTo, Fin.forall_fin_succ, FinVec.sum, Set.SurjOn, Set.subset_def]
    and_intros; tauto
    intro x _ _ _ _ _; use x 0, x 1, x 2, x 3; simp [*]; exact FinVec.etaExpand_eq x
  _ = Nat.choose 6 3 := FinVec.composition_pos_card _ _

theorem Zad6 (n k : ℕ) : ∑ j ∈ range n, j.choose k = n.choose (k + 1) := by
  cases n; simp; rename_i n
  rw [← Nat.sum_Icc_choose]; apply sum_congr_of_eq_on_inter <;> grind

theorem Zad7 (n k : ℕ) : ∑ j ∈ range (k + 1), (n + j).choose j = (n + k + 1).choose k := by
  convert Nat.sum_range_add_choose k n using 1
  · congr; funext j; rw [add_comm, Nat.choose_symm_add]
  · rw [add_comm n]; exact Nat.choose_symm_of_eq_add (add_assoc _ _ _)

theorem Zad8 (n : ℕ) : #{f : Fin n → Fin n | Monotone f} = (2 * n - 1).choose n :=
  calc #{f : Fin n → Fin n | Monotone f}
  _ = #{f : Fin n → Fin (2 * n - 1) | StrictMono f} := by
    apply card_nbij (fun f i => ((f i).addNat i).castLE (by lia))
      <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, funext_iff]
    · simp [Monotone, StrictMono, ← Fin.val_fin_lt, ← Fin.val_fin_le]
      exact fun f hf a b h => add_lt_add_of_le_of_lt (hf h.le) h
    · cases n; · simp [Monotone]
      intro f hf; exists fun i => ⟨f i - i, ?_⟩; swap; simp [Fin.ext_iff]; and_intros
      · simp [Fin.monotone_iff_le_succ]; intro i; grind [hf i.castSucc_lt_succ]
      · intro i; apply Nat.sub_add_cancel; induction i using Fin.induction; · simp
        rename_i i ih; simp at *; grw [ih]; exact hf i.castSucc_lt_succ
      · rename_i n; induction i using Fin.reverseInduction; · grind
        rename_i i ih; simp at *; grw [← Nat.lt_add_one_iff, add_assoc, ← ih]
        exact hf i.castSucc_lt_succ
  _ = ((univ : Finset (Fin (2 * n - 1))).powersetCard n).card := by
    apply card_bij (fun f h => univ.map ⟨f, StrictMono.injective (by simp_all)⟩)
      <;> simp [← coe_inj]
    · exact fun f hf g hg => (hf.range_inj hg).mp
    · intro s h; exists s.orderEmbOfFin h; simp [StrictMono]
  _ = (2 * n - 1).choose n := by simp

-- TODO: Zad9

theorem Zad10 (n k : ℕ) : ∑ i ≤ k, n.choose i * (n - i).choose (k - i) = 2 ^ k * n.choose k := by
  let F : Finset (Finset (Fin n) × Finset (Fin n)) := {(s, t) : _ | #s = k ∧ t ⊆ s}
  have h1 := calc #F
    _ = ∑ s ∈ powersetCard k univ, #{st ∈ F | st.1 = s} :=
      card_eq_sum_card_fiberwise (by simp [Set.MapsTo, F]; tauto)
    _ = ∑ s ∈ powersetCard k (univ : Finset (Fin n)), #s.powerset := by
      apply sum_congr rfl; intro s hs; simp at hs; apply card_nbij Prod.snd <;>
        simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> grind
    _ = ∑ s ∈ powersetCard k (univ : Finset (Fin n)), 2 ^ k := by
      congr! with s hs; simp_all
    _ = 2 ^ k * n.choose k := by simp [mul_comm]
  have h2 := calc #F
    _ = ∑ i ≤ k, #{st ∈ F | #st.2 = i} := card_eq_sum_card_fiberwise
      (by simp [Set.MapsTo, F]; intro s t hs ht; exact hs ▸ card_le_card ht)
    _ = ∑ i ≤ k, ∑ t ∈ powersetCard i univ, #{st ∈ F | st.2 = t} := by
      congr! with i hi; rw [card_eq_sum_card_fiberwise (f := Prod.snd)]
      · congr! 2 with t ht; simp [filter_filter] at *; congr; grind
      · simp [Set.MapsTo]
    _ = ∑ i ≤ k, ∑ t ∈ powersetCard i univ, #{s | #s = k - i ∧ Disjoint t s} := by
      congr! with i hi t ht; apply card_nbij fun st => st.1 \ t <;> try first | infer_instance |
        simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, disjoint_sdiff, F]
      · intro s t hs h ht; simp_all [card_sdiff_of_subset]
      · intro s t' hs ht' rfl s' t hs' ht'' rfl h; simp; rw [← sdiff_left_inj ht' ht'']; assumption
      · intro s hs hd; exists t ∪ s; simp_all [union_sdiff_cancel_left]
    _ = ∑ i ≤ k, ∑ t ∈ powersetCard i univ, #((univ \ t).powersetCard (k - i)) := by
      congr!; ext s; simp [disjoint_right, subset_iff]; tauto
    _ = ∑ i ≤ k, n.choose i * (n - i).choose (k - i) := by
      congr! with i hi; convert sum_const_nat ?_ <;> simp
      intro t ht; simp [card_univ_sdiff, ht]
  simp_all

theorem Zad11a (n : ℕ) : ∑ k ≤ n, k * n.choose k = n * 2 ^ (n - 1) := by
  apply and_self_iff.mp; and_intros
  · let F : Finset (Finset (Fin n) × Fin n) := {(s, x) : _ | x ∈ s}
    have h1 := calc #F
      _ = ∑ s, #{sx ∈ F | sx.1 = s} := card_eq_sum_card_fiberwise (by simp [Set.MapsTo])
      _ = ∑ s : Finset (Fin n), #s := by congr with s; apply card_nbij Prod.snd
          <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, F] <;> grind only
      _ = ∑ k ≤ n, n.choose k * k := by
        convert! sum_powerset_apply_card id using 2 <;> simp [Nat.range_succ_eq_Iic]
      _ = ∑ k ≤ n, k * n.choose k := by congr! 1; ring
    have h2 := calc #F
      _ = ∑ x : Fin n, #(univ \ {x}).powerset := by
        rw [card_eq_sum_card_fiberwise (f := Prod.snd)]
        · congr; ext x; apply card_nbij (compl ∘ Prod.fst)
            <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> try grind
          intro s h; exists sᶜ; simpa [F]
        · simp [Set.mapsTo_univ]
      _ = n * 2 ^ (n - 1) := by convert sum_const_nat ?_ <;> simp [card_univ_sdiff]
    simp_all
  · rw [← Nat.sum_range_mul_choose]; congr; ext; simp

theorem Zad11b {n : ℕ} (hn : 1 < n) : ∑ k ≤ n, k ^ 2 * n.choose k = (n + n ^ 2) * 2 ^ (n - 2) := by
  apply and_self_iff.mp; and_intros
  · let F : Finset (Finset (Fin n) × Fin n × Fin n) := {(s, x, y) : _ | x ∈ s ∧ y ∈ s}
    have h1 := calc #F
      _ = ∑ s, #{sxy ∈ F | sxy.1 = s} := card_eq_sum_card_fiberwise (by simp [Set.MapsTo])
      _ = ∑ s : Finset (Fin n), #(s ×ˢ s) := by congr with s; apply card_nbij Prod.snd
          <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, F] <;> grind only
      _ = ∑ k ≤ n, n.choose k * k ^ 2 := by
        convert! sum_powerset_apply_card (· ^ 2) using 2 <;> simp [sq, Nat.range_succ_eq_Iic]
      _ = ∑ k ≤ n, k ^ 2 * n.choose k := by grind
    have h2 := calc #F
      _ = ∑ xy : Fin n × Fin n, #(univ \ {xy.1, xy.2}).powerset := by
        rw [card_eq_sum_card_fiberwise (f := Prod.snd)]
        · congr; ext x; apply card_nbij (compl ∘ Prod.fst)
            <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> try grind
          intro s h; exists sᶜ; simp [F]; grind
        · simp [Set.mapsTo_univ]
      _ = ∑ xy : Fin n × Fin n with xy.1 = xy.2, #(univ \ {xy.1, xy.2}).powerset +
          ∑ xy : Fin n × Fin n with xy.1 ≠ xy.2, #(univ \ {xy.1, xy.2}).powerset :=
          (sum_filter_add_sum_filter_not _ _ _).symm
      _ = n * 2 ^ (n - 1) + (n * n - n) * 2 ^ (n - 2) := by
        have : #{xy : Fin n × Fin n | xy.1 = xy.2} = n := by
          apply card_eq_of_bijective fun i h => (⟨i, h⟩, ⟨i, h⟩) <;> simp [← Fin.val_inj]
        congr <;> convert sum_const_nat ?_ <;>
          simp [this, filter_not, card_univ_sdiff]; intro a b h; simp [h]
      _ = 2 * n * 2 ^ (n - 2) + (n ^ 2 - n) * 2 ^ (n - 2) := by
        conv => rhs; lhs; rw [mul_comm 2, mul_assoc, show n - 2 = n - 1 - 1 by lia,
          mul_pow_sub_one (by lia)]
        simp [sq]
      _ = (n + n ^ 2) * 2 ^ (n - 2) := by
        rw [← add_mul, two_mul, add_add_tsub_cancel (Nat.le_pow two_pos)]
    simp_all
  · induction n, hn using Nat.le_induction
    · simp; conv => lhs; whnf
    · rename_i n hn ih; simp [Iic_eq_Icc, ← insert_Icc_add_one_left_eq_Icc (a := 0)]
      calc ∑ k ∈ Icc 1 (n + 1), k ^ 2 * (n + 1).choose k
      _ = ∑ k ∈ Icc 1 (n + 1), k ^ 2 * (n.choose (k - 1) + n.choose k) := by
        congr! 2 with k hk; simp at hk; exact Nat.choose_succ_left n k hk.left
      _ = ∑ k ∈ Icc 1 (n + 1), k ^ 2 * n.choose (k - 1) +
          ∑ k ∈ Icc 1 (n + 1), k ^ 2 * n.choose k := by simp [mul_add, sum_add_distrib]
      _ = ∑ k ≤ n, (k + 1) ^ 2 * n.choose k + ∑ k ∈ Icc 1 (n + 1), k ^ 2 * n.choose k := by
        congr 1; symm; convert! sum_Ico_add _ _ _ 1 using 2; simp [add_comm]
      _ = ∑ k ≤ n, (k + 1) ^ 2 * n.choose k + ∑ k ≤ n, k ^ 2 * n.choose k := by
        simp [Iic_eq_Icc, ← insert_Icc_add_one_left_eq_Icc (a := 0),
          ← insert_Icc_right_eq_Icc_add_one, Nat.choose_eq_zero_of_lt]
      _ = 2 * ∑ k ≤ n, k ^ 2 * n.choose k + 2 * ∑ k ≤ n, k * n.choose k + ∑ k ≤ n, n.choose k := by
        simp [add_sq, add_mul, sum_add_distrib, two_mul]; ac_rfl
      _ = 2 * ((n + n ^ 2) * 2 ^ (n - 2)) + 2 * (n * 2 ^ (n - 1)) + 2 ^ n := by
        simp [ih, Zad11a, ← Nat.sum_range_choose, Nat.range_succ_eq_Iic]
      _ = (n + 1 + (n + 1) ^ 2) * 2 ^ (n - 1) := by rw [show n = n - 2 + 2 by lia]; simp; ring

theorem Zad11c (m n k : ℕ) : ∑ i ≤ k, m.choose i * n.choose (k - i) = (m + n).choose k := by
  apply and_self_iff.mp; and_intros
  · symm; calc (m + n).choose k
    _ = #((univ (α := Fin m ⊕ Fin n)).powersetCard k) := by simp
    _ = #{s : Finset (Fin m) × Finset (Fin n) | #s.1 + #s.2 = k} := by
      apply card_equiv sumEquiv.toEquiv
      simp [sumEquiv_apply_fst, sumEquiv_apply_snd, card_toLeft_add_card_toRight]
    _ = ∑ i ≤ k, #{s : Finset _ × Finset _ | #s.1 = i ∧ #s.2 = k - i} := by
      rw [card_eq_sum_card_fiberwise (f := fun s => #s.1)]
      · congr! 2; ext; grind
      · simp [Set.MapsTo]; lia
    _ = ∑ i ≤ k, #{s : Finset (Fin m) | #s = i} * #{s : Finset (Fin n) | #s = k - i} := by
      congr! with i; rw [← card_product]; congr; ext; simp
    _ = ∑ i ≤ k, m.choose i * n.choose (k - i) := by simp
  · rw [Nat.add_choose_eq, Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.range_succ_eq_Iic]
