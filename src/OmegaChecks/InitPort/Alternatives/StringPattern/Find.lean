module
import all Init.Data.String.Lemmas.Pattern.Find.Char
import all Init.Data.String.Lemmas.Pattern.Find.Pred
import all Init.Data.String.Lemmas.Pattern.Find.Basic
import all Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Lemmas.Pattern.Char

/-! Read the first accepted character and rule out every earlier position in the searched slice. -/

namespace OmegaChecks.InitPort.Alternatives.String.Slice

open _root_.String.Slice Pattern.Model

public theorem find?_bool_eq_some_iff : type_of% @_root_.String.Slice.find?_bool_eq_some_iff := by
  intro p s pos
  refine (find?_eq_some_iff p).trans ⟨?_, ?_⟩
  · rintro ⟨yes, first⟩
    obtain ⟨h, accepted⟩ := CharPred.matchesAt_iff.mp yes
    exact ⟨h, accepted, fun q before => Bool.eq_false_iff.mpr fun accepted =>
      first q before (CharPred.matchesAt_iff.mpr ⟨_, accepted⟩)⟩
  · rintro ⟨h, accepted, first⟩
    refine ⟨CharPred.matchesAt_iff.mpr ⟨h, accepted⟩, fun q before yes => ?_⟩
    obtain ⟨_, ok⟩ := CharPred.matchesAt_iff.mp yes
    exact Bool.noConfusion ((first q before).symm.trans ok)

public theorem Pos.find?_bool_eq_some_iff : type_of% @_root_.String.Slice.Pos.find?_bool_eq_some_iff := by
  intro p s start pos
  refine posFind?_eq_some_iff.trans ⟨?_, ?_⟩
  · rintro ⟨lo, yes, first⟩
    exact ⟨lo, CharPred.matchesAt_iff.mp yes, fun q hq before => Bool.eq_false_iff.mpr fun ok =>
      first q hq before (CharPred.matchesAt_iff.mpr ⟨_, ok⟩)⟩
  · rintro ⟨lo, yes, first⟩
    refine ⟨lo, CharPred.matchesAt_iff.mpr yes, fun q hq before matchAt => ?_⟩
    obtain ⟨_, ok⟩ := CharPred.matchesAt_iff.mp matchAt
    exact Bool.noConfusion ((first q hq before).symm.trans ok)

public theorem Pos.find?_bool_eq_none_iff : type_of% @_root_.String.Slice.Pos.find?_bool_eq_none_iff := by
  intro p s start
  refine posFind?_eq_none_iff.trans ⟨?_, ?_⟩
  · exact fun absent q lo h => Bool.eq_false_iff.mpr fun yes =>
      absent q lo (CharPred.matchesAt_iff.mpr ⟨h, yes⟩)
  · intro first q lo matched
    obtain ⟨h, ok⟩ := CharPred.matchesAt_iff.mp matched
    exact Bool.noConfusion ((first q lo h).symm.trans ok)

public theorem find?_char_eq_some_iff : type_of% @_root_.String.Slice.find?_char_eq_some_iff := by
  intro c s pos
  refine (find?_eq_some_iff c).trans ⟨?_, ?_⟩
  · rintro ⟨yes, first⟩
    obtain ⟨h, eq⟩ := Pattern.Model.Char.matchesAt_iff.mp yes
    exact ⟨h, eq, fun q before ok => first q before (Pattern.Model.Char.matchesAt_iff.mpr ⟨_, ok⟩)⟩
  · rintro ⟨h, eq, first⟩
    refine ⟨Pattern.Model.Char.matchesAt_iff.mpr ⟨h, eq⟩, fun q before yes => ?_⟩
    obtain ⟨_, ok⟩ := Pattern.Model.Char.matchesAt_iff.mp yes
    exact first q before ok

public theorem Pos.find?_char_eq_some_iff : type_of% @_root_.String.Slice.Pos.find?_char_eq_some_iff := by
  intro c s start pos
  refine posFind?_eq_some_iff.trans ⟨?_, ?_⟩
  · rintro ⟨lo, yes, first⟩
    exact ⟨lo, Pattern.Model.Char.matchesAt_iff.mp yes, fun q hq before ok =>
      first q hq before (Pattern.Model.Char.matchesAt_iff.mpr ⟨_, ok⟩)⟩
  · rintro ⟨lo, yes, first⟩
    refine ⟨lo, Pattern.Model.Char.matchesAt_iff.mpr yes, fun q hq before matchAt => ?_⟩
    obtain ⟨_, ok⟩ := Pattern.Model.Char.matchesAt_iff.mp matchAt
    exact first q hq before ok

public theorem Pos.find?_char_eq_none_iff : type_of% @_root_.String.Slice.Pos.find?_char_eq_none_iff := by
  intro c s start
  refine posFind?_eq_none_iff.trans ⟨?_, ?_⟩
  · exact fun absent q lo h ok => absent q lo (Pattern.Model.Char.matchesAt_iff.mpr ⟨h, ok⟩)
  · intro first q lo matched
    obtain ⟨h, ok⟩ := Pattern.Model.Char.matchesAt_iff.mp matched
    exact first q lo h ok

public theorem contains_char_eq : type_of% @_root_.String.Slice.contains_char_eq := by
  intro c s
  apply Bool.eq_iff_iff.mpr
  refine (contains_eq_true_iff c).trans (Iff.trans ?_ decide_eq_true_iff.symm)
  constructor
  · rintro ⟨pos, yes⟩
    obtain ⟨h, ok⟩ := Pattern.Model.Char.matchesAt_iff.mp yes
    exact mem_toList_copy_iff_exists_get.mpr ⟨pos, h, ok⟩
  · intro mem
    obtain ⟨pos, h, ok⟩ := mem_toList_copy_iff_exists_get.mp mem
    exact ⟨pos, Pattern.Model.Char.matchesAt_iff.mpr ⟨h, ok⟩⟩

public theorem contains_bool_eq : type_of% @_root_.String.Slice.contains_bool_eq := by
  intro p s
  apply Bool.eq_iff_iff.mpr
  refine (contains_eq_true_iff p).trans (Iff.trans ?_ List.any_eq_true.symm)
  constructor
  · rintro ⟨pos, yes⟩
    obtain ⟨h, ok⟩ := CharPred.matchesAt_iff.mp yes
    exact ⟨_, mem_toList_copy_iff_exists_get.mpr ⟨pos, h, rfl⟩, ok⟩
  · rintro ⟨c, mem, ok⟩
    obtain ⟨pos, h, rfl⟩ := mem_toList_copy_iff_exists_get.mp mem
    exact ⟨pos, CharPred.matchesAt_iff.mpr ⟨h, ok⟩⟩

end OmegaChecks.InitPort.Alternatives.String.Slice

namespace OmegaChecks.InitPort.Alternatives.String

public theorem contains_char_eq : type_of% @_root_.String.contains_char_eq := by
  intro c s
  exact (_root_.String.Slice.contains_char_eq (s := s.toSlice) (c := c)).trans
    (congrArg (fun t : String => decide (c ∈ t.toList)) s.copy_toSlice)

public theorem contains_bool_eq : type_of% @_root_.String.contains_bool_eq := by
  intro p s
  exact (_root_.String.Slice.contains_bool_eq (s := s.toSlice) (p := p)).trans
    (congrArg (fun t : String => t.toList.any p) s.copy_toSlice)

public theorem contains_prop_eq : type_of% @_root_.String.contains_prop_eq := by
  intro p inst s
  exact _root_.String.contains_prop_eq_contains_decide.trans _root_.String.contains_bool_eq

end OmegaChecks.InitPort.Alternatives.String
