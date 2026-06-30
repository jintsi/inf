import Std.Do.Triple.SpecLemmas

/-! ### Some tidbits for working with unbundled `List.Cursor`s and ranges -/

open Std.PRange

theorem Std.Rio.length_pref_le [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Rxo.HasSize α]
    [Rxo.LawfulHasSize α] {r : Rio α} (h : r.toList = pref ++ suf) : pref.length ≤ r.size := by
  simp [← length_toList, congrArg List.length h]

theorem Nat.length_pref_le_rio {b : Nat} (h : (*...b).toList = pref ++ suf) :
    pref.length ≤ b := by simpa using (*...b).length_pref_le h

theorem Std.Rci.cur_mem [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxi.IsAlwaysFinite α] {r : Rci α}
  (h : r.toList = pref ++ cur :: suf) : cur ∈ r := by simp [← mem_toList_iff_mem, h]

theorem Std.Roi.cur_mem [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {r : Roi α}
    (h : r.toList = pref ++ cur :: suf) : cur ∈ r := by simp [← mem_toList_iff_mem, h]

theorem Std.Roi.cur_ne_pref [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    {r : Roi α} (h : r.toList = pref ++ cur :: suf) {a : α} (ha : a ∈ pref) : cur ≠ a := by
  have := r.pairwise_toList_ne; simp [h, List.pairwise_append] at this
  symm; exact (this.2.2 a ha).1

theorem Nat.toList_rio_eq_range' {b : Nat} : (*...b).toList = List.range' 0 b := by
  induction b with simp [toList_rio_succ, ← List.range'_append_1, *]

theorem Nat.length_pref_rio {b : Nat} (h : (*...b).toList = pref ++ cur :: suf) :
    pref.length = cur := by
  rw [Nat.toList_rio_eq_range'] at h; rw [List.eq_of_range'_eq_append_cons h]; simp
