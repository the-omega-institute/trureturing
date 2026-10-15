/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreEdgeClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCoreEdgeClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete native T surgery excludes every literal old cut. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreEdgeClassification

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing

private theorem cutGenerator_native {m : ℕ} (p : Fin m ⊕ Fin (m - 2)) :
    cutGenerator p = a m ∨ cutGenerator p = b m := by
  cases p with
  | inl i => simp only [cutGenerator]; split <;> simp
  | inr j => exact Or.inr rfl

private theorem c_ne_native {m : ℕ} (hm : 4 ≤ m) (g : Configuration m)
    (hg : g = a m ∨ g = b m) : c m ≠ g := by
  rcases hg with rfl | rfl
  · intro he
    have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) he
    simp only [c_apply, Fin.val_last, a_apply, Fin.val_rev, Nat.sub_self] at hv
    rw [if_neg (by omega : ¬ m < m - 1)] at hv
    omega
  · intro he
    let i : Fin (m + 1) := ⟨m - 1, by omega⟩
    have hv := congrArg (fun f : Configuration m => (f i).val) he
    simp only [c_apply, b_apply, i, lt_self_iff_false, if_false, Nat.sub_self] at hv
    rw [if_pos (by omega : m - 1 < m)] at hv
    omega

private theorem edge_generator_unique {m : ℕ} (x y g h : Configuration m)
    (hg : g * g = 1) (he : s(x, x * g) = s(y, y * h)) : g = h := by
  rcases Sym2.eq_iff.mp he with ⟨hxy, hend⟩ | ⟨hxy, hend⟩
  · subst y
    exact mul_left_cancel hend
  · rw [← hend] at hxy
    have hgh : g * h = 1 := mul_left_cancel (by
      simpa only [mul_assoc, mul_one] using hxy.symm)
    have ht := congrArg (g * ·) hgh
    simpa only [← mul_assoc, hg, one_mul, mul_one] using ht.symm

/-- None of the independently enumerated T old cuts belongs to the complete
uncut-circle or c-seam edge set. Ownership excludes another circle's retained
edge, and actual generator coordinates exclude every c seam. -/
theorem native_t_deleted_edge_disjoint {m : ℕ} (hm : 4 ≤ m)
    (e : Sym2 (Configuration m)) (hdel : CoreDeletedEdge m e) :
    ¬ (CoreUncut m e ∨ TSeam m e) := by
  obtain ⟨q, heq⟩ := hdel
  rintro (⟨p, hp, hne⟩ | ⟨p, hep⟩)
  · have hxq : cutStart q ∈ e := heq ▸ Sym2.mem_mk_left _ _
    have hxp := native_circle_edge_endpoint (cutStart p) (cutStart q) e hp hxq
    have howner : p = q := native_t_circle_owner_unique hm (cutStart q) p q
      ((native_cut_circle_iff hm p _).mp hxp)
      ((native_cut_circle_iff hm q _).mp (Or.inl rfl))
    subst p
    exact hne heq
  · have hlabel : c m = cutGenerator q := edge_generator_unique
      (cutStart p * cutGenerator p) (cutStart q) (c m) (cutGenerator q)
      (c_sq m) (hep.symm.trans heq)
    exact c_ne_native hm (cutGenerator q) (cutGenerator_native q) hlabel

#print axioms native_t_deleted_edge_disjoint

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreEdgeClassification
