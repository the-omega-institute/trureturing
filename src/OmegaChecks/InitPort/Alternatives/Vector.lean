module
public import OmegaChecks.InitPort.Alternatives.VectorDecisions
public import OmegaChecks.InitPort.Alternatives.VectorFind
public import OmegaChecks.InitPort.Alternatives.VectorNested
public import OmegaChecks.InitPort.Alternatives.VectorNumeric
import all Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Monadic

/-! Fixed-length array lookup, replacement and decision laws. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem Vector.getElem?_eq_none_iff : type_of% @_root_.Vector.getElem?_eq_none_iff := by
  intro α n i xs
  obtain ⟨data, rfl⟩ := xs
  exact _root_.Array.getElem?_eq_none_iff

public theorem Vector.none_eq_getElem?_iff : type_of% @_root_.Vector.none_eq_getElem?_iff := by
  intro α n xs i
  obtain ⟨data, rfl⟩ := xs
  exact _root_.Array.none_eq_getElem?_iff

public theorem Vector.getElem?_push : type_of% @_root_.Vector.getElem?_push := by
  intro α n xs x i
  rw [← _root_.Vector.getElem?_toArray, _root_.Vector.toArray_push, _root_.Array.getElem?_push,
    _root_.Vector.size_toArray, _root_.Vector.getElem?_toArray]

public theorem Vector.getElem_zipWith : type_of% @_root_.Vector.getElem_zipWith := by
  intro α β γ n f xs ys i hi
  apply _root_.Array.getElem_zipWith

public theorem Vector.any_congr : type_of% @_root_.Vector.any_congr := by
  intro α n xs ys rfl p q h
  exact _root_.Array.any_congr (xs := xs.toArray) rfl h rfl rfl

public theorem Vector.all_congr : type_of% @_root_.Vector.all_congr := by
  intro α n xs ys rfl p q h
  exact _root_.Array.all_congr (xs := xs.toArray) rfl h rfl rfl

public theorem Vector.any_beq' : type_of% @_root_.Vector.any_beq' := by
  intro α n a _ _ xs
  exact _root_.Array.any_beq' (xs := xs.toArray)

public theorem Vector.all_bne' : type_of% @_root_.Vector.all_bne' := by
  intro α n a _ _ xs
  exact _root_.Array.all_bne' (xs := xs.toArray)

public theorem Vector.any_eq_not_all_not : type_of% @_root_.Vector.any_eq_not_all_not := by
  intro α n xs p
  exact _root_.Array.any_eq_not_all_not (xs := xs.toArray)

public theorem Vector.all_eq_false : type_of% @_root_.Vector.all_eq_false := by
  intro α n p xs
  obtain ⟨data, rfl⟩ := xs
  exact _root_.Array.all_eq_false

public theorem Vector.all_eq : type_of% @_root_.Vector.all_eq := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.Vector.all_eq_true.trans decide_eq_true_iff.symm)

public theorem Vector.all_eq' : type_of% @_root_.Vector.all_eq' := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.Vector.all_eq_true'.trans decide_eq_true_iff.symm)

public theorem Vector.decide_forall_mem : type_of% @_root_.Vector.decide_forall_mem := by
  intros
  apply Bool.eq_iff_iff.mpr
  refine decide_eq_true_iff.trans (Iff.trans ?_ _root_.Vector.all_eq_true'.symm)
  exact ⟨fun h x mem => decide_eq_true (h x mem), fun h x mem => of_decide_eq_true (h x mem)⟩

public theorem Vector.contains_iff_exists_mem_beq : type_of% @_root_.Vector.contains_iff_exists_mem_beq := by
  intro α n _ xs a
  rw [← _root_.Vector.contains_toArray]
  refine _root_.Array.contains_iff_exists_mem_beq.trans ?_
  exact ⟨fun ⟨x, mem, hit⟩ => ⟨x, (_root_.Vector.mem_toArray_iff ..).mp mem, hit⟩,
    fun ⟨x, mem, hit⟩ => ⟨x, (_root_.Vector.mem_toArray_iff ..).mpr mem, hit⟩⟩

public theorem Vector.map_inj_right : type_of% @_root_.Vector.map_inj_right := by
  intro α β n xs ys f inj
  constructor
  · intro h
    apply _root_.Vector.toArray_inj.mp
    exact (_root_.Array.map_inj_right inj).mp (congrArg _root_.Vector.toArray h)
  · intro h
    cases h
    rfl

public theorem Vector.replace_of_not_mem : type_of% @_root_.Vector.replace_of_not_mem := by
  intro α _ _ n a b xs ne
  apply _root_.Vector.toArray_inj.mp
  exact _root_.Array.replace_of_not_mem (fun h => ne ((_root_.Vector.mem_toArray_iff ..).mp h))

public theorem Vector.replace_append_left : type_of% @_root_.Vector.replace_append_left := by
  intro α _ _ n m a b xs ys hit
  apply _root_.Vector.toArray_inj.mp
  exact _root_.Array.replace_append_left ((_root_.Vector.mem_toArray_iff ..).mpr hit)

public theorem Vector.replace_append_right : type_of% @_root_.Vector.replace_append_right := by
  intro α _ _ n m a b xs ys miss
  apply _root_.Vector.toArray_inj.mp
  exact _root_.Array.replace_append_right (fun h => miss ((_root_.Vector.mem_toArray_iff ..).mp h))

public theorem Vector.replace_append : type_of% @_root_.Vector.replace_append := by
  intro α _ _ n m a b xs ys
  by_cases hit : a ∈ xs
  · exact (_root_.Vector.replace_append_left hit).trans (ite_eq_left hit).symm
  · exact (_root_.Vector.replace_append_right hit).trans (ite_eq_right hit).symm

public theorem Vector.getElem_replace_of_ne : type_of% @_root_.Vector.getElem_replace_of_ne := by
  intro α _ _ n a b xs i hi miss
  obtain ⟨data, rfl⟩ := xs
  exact _root_.Array.getElem_replace_of_ne (h := hi) miss


public theorem Vector.anyM_congr : type_of% @_root_.Vector.anyM_congr := by
  intro m α n inst xs ys rfl p q h
  exact Array.anyM_congr (xs := xs.toArray) rfl h rfl rfl

public theorem Vector.allM_congr : type_of% @_root_.Vector.allM_congr := by
  intro m α n inst xs ys rfl p q h
  exact Array.allM_congr (xs := xs.toArray) rfl h rfl rfl

public theorem Vector.foldlM_map : type_of% @_root_.Vector.foldlM_map := by
  intros
  unfold Vector.foldlM
  rw [Vector.toArray_map, Array.size_map]
  exact Array.foldlM_map (w := rfl)

public theorem Vector.foldrM_map : type_of% @_root_.Vector.foldrM_map := by
  intros
  unfold Vector.foldrM
  rw [Vector.toArray_map, Array.size_map]
  exact Array.foldrM_map (w := rfl)

private theorem attachWithFromAttach {xs : Vector α n} {q : α → Prop} (h : ∀ a ∈ xs, q a) :
    xs.attachWith q h = xs.attach.map (fun x => ⟨x.val, h _ x.property⟩) := by
  apply Vector.ext
  intro i hi
  exact Subtype.ext (by rw [Vector.getElem_map, Vector.getElem_attach, Vector.getElem_attachWith])

public theorem Vector.foldlM_attachWith : type_of% @_root_.Vector.foldlM_attachWith := by
  intro m α n β mon xs q H f b
  rw [attachWithFromAttach H]
  exact Vector.foldlM_map

public theorem Vector.foldrM_attachWith : type_of% @_root_.Vector.foldrM_attachWith := by
  intro m α n β mon law xs q H f b
  rw [attachWithFromAttach H]
  exact Vector.foldrM_map

public theorem Vector.idRun_forIn'_yield_eq_foldl : type_of% @_root_.Vector.idRun_forIn'_yield_eq_foldl := by
  intros
  exact Vector.forIn'_pure_yield_eq_foldl (m := Id) _ _

public theorem Vector.idRun_forIn_yield_eq_foldl : type_of% @_root_.Vector.idRun_forIn_yield_eq_foldl := by
  intros
  exact Vector.forIn_pure_yield_eq_foldl (m := Id) _ _

end OmegaChecks.InitPort.Alternatives
