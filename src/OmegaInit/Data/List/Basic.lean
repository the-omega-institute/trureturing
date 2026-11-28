module
public import Init.Data.List.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.eraseIdx.match_1 List.modifyHead.eq_1 List.modifyHead.eq_2 List.reverseAux.match_1 List.take.match_1)
end Omega
namespace Omega.List
export _root_.List (Mem Perm appendTR append_assoc append_cons append_eq append_nil concat_eq_append cons_append drop drop_eq_nil_of_le drop_nil eraseIdx eraseIdx_cons_zero eraseIdx_nil filter filterMap filterMap_nil filter_nil flatMap_append flatMap_cons flatMap_nil flatten_cons flatten_nil foldl_cons foldl_nil foldr foldr_cons foldr_nil head? head?_cons head?_nil headD headD_cons headD_nil instAppend instMembership isEmpty isEmpty_cons isEmpty_nil length_add_eq_lengthTRAux length_append length_concat length_cons length_nil length_replicate length_singleton map_cons map_nil mem_append_left mem_append_right modifyHead modifyHead_cons modifyHead_nil nil_append replicate replicate_succ replicate_zero reverse reverseAux reverseAux_cons reverseAux_eq_append reverseAux_nil reverseAux_reverseAux reverse_cons reverse_nil singleton tail tail? tail?_cons tail?_nil tailD tailD_cons tailD_nil tail_cons tail_nil)
end Omega.List
namespace Omega.List.Mem
export _root_.List.Mem (casesOn head rec recOn tail)
end Omega.List.Mem
namespace Omega.List.Perm
export _root_.List.Perm (casesOn cons nil rec recOn swap trans)
end Omega.List.Perm
