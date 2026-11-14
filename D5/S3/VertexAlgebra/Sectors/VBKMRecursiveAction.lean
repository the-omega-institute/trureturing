/- GID: D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMRecursiveAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
proof_shape: ASSUMED-UNVERIFIED until the port is compiled and classified.
escape_witness: ASSUMED-UNVERIFIED until the port is compiled and classified.
Direct frozen dependencies: none.
-/

import D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Interval
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Common
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction


noncomputable def basisWord (w : (List (Bool ⊕ ℕ+))) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) := Finsupp.single w 1

noncomputable def left (g : (Bool ⊕ ℕ+)) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (List.cons g)

theorem left_basis (g : (Bool ⊕ ℕ+)) (w : (List (Bool ⊕ ℕ+))) :
    left g (basisWord w) = basisWord (g::w) := by
  simp [left,basisWord]

noncomputable def prepend (u : (List (Bool ⊕ ℕ+))) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (u ++ ·)

noncomputable def relation (r s : ℕ+) (v : (List (Bool ⊕ ℕ+))) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  basisWord (.inr r :: .inr s :: v) - basisWord (.inr s :: .inr r :: v) -
    ((s.val : ℂ) - (r.val : ℂ)) • basisWord (.inr (r+s) :: v)

noncomputable def relations : Set ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  {x | ∃ (u v : (List (Bool ⊕ ℕ+))) (r s : ℕ+), x = prepend u (relation r s v)}

noncomputable def N : Submodule ℂ ((List (Bool ⊕ ℕ+)) →₀ ℂ) := Submodule.span ℂ relations

private theorem relation_mem (r s : ℕ+) (u v : (List (Bool ⊕ ℕ+))) :
    prepend u (relation r s v) ∈ N := by
  exact Submodule.subset_span ⟨u,v,r,s,rfl⟩

theorem leftPreserves (g : (Bool ⊕ ℕ+)) {x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)} (hx : x ∈ N) : left g x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u,v,r,s,rfl⟩ := hy
    have hp : (left g).comp (prepend u) = prepend (g::u) := by
      apply Finsupp.lhom_ext
      intro w c
      simp [LinearMap.comp_apply,left,prepend,Finsupp.lmapDomain_apply]
    change ((left g).comp (prepend u)) (relation r s v) ∈ N
    rw [hp]
    exact relation_mem r s (g::u) v
  | zero => simp
  | add y z hy hz ihy ihz => simpa only [map_add] using Submodule.add_mem N ihy ihz
  | smul c y hy ih => simpa only [map_smul] using Submodule.smul_mem N c ih

end D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
namespace D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
noncomputable def tokenWeight (a : ℂ × ℂ) : (Bool ⊕ ℕ+) → ℂ
  | .inl i => if i then 4/3*a.1+a.2 else a.1+2/3*a.2
  | .inr r => (r.val : ℂ)/3*(a.1+a.2)

noncomputable def wordWeight (a : ℂ × ℂ) (w : (List (Bool ⊕ ℕ+))) : ℂ :=
  (w.map (tokenWeight a)).sum

noncomputable def cartan (a : ℂ × ℂ) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun w => wordWeight a w • basisWord w)

private theorem cartan_basis (a : ℂ × ℂ) (w : (List (Bool ⊕ ℕ+))) :
    cartan a (basisWord w) = wordWeight a w • basisWord w := by
  simp [cartan,basisWord]

noncomputable def raisingWord (i : Bool) : (List (Bool ⊕ ℕ+)) → ((List (Bool ⊕ ℕ+)) →₀ ℂ)
  | [] => 0
  | .inl k :: w => left (.inl k) (raisingWord i w) +
      if i=k then cartan (if i then (1,0) else (0,1)) (basisWord w) else 0
  | .inr r :: w => left (.inr r) (raisingWord i w)

noncomputable def raising (i : Bool) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (raisingWord i)

private theorem raising_basis (i : Bool) (w : (List (Bool ⊕ ℕ+))) :
    raising i (basisWord w) = raisingWord i w := by
  simp [raising,basisWord]

private theorem raising_mode_commute (i : Bool) (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    raising i (left (.inr r) x) = left (.inr r) (raising i x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | single w c =>
    simp [left, raising, basisWord, raisingWord, Finsupp.linearCombination_apply]
  | add x y hx hy => simp only [map_add,hx,hy]


private theorem cartan_left (a : ℂ × ℂ) (g : (Bool ⊕ ℕ+)) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    cartan a (left g x) = left g (cartan a x) + tokenWeight a g • left g x := by
  have hh : (cartan a).comp (left g) = (left g).comp (cartan a) + tokenWeight a g • left g := by
    apply Finsupp.lhom_ext
    intro w c
    have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
    simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.smul_apply,hs,
      map_smul,left_basis,cartan_basis]
    simp only [wordWeight,List.map_cons,List.sum_cons]
    module
  exact LinearMap.congr_fun hh x

private theorem cartan_relation (a : ℂ × ℂ) (r s : ℕ+) (v : (List (Bool ⊕ ℕ+))) :
    cartan a (relation r s v) =
      (tokenWeight a (.inr r) + tokenWeight a (.inr s) + wordWeight a v) • relation r s v := by
  simp only [relation,map_sub,map_smul,cartan_basis]
  simp [wordWeight,tokenWeight,PNat.add_coe,Nat.cast_add]
  module

private theorem prepend_cons (g : (Bool ⊕ ℕ+)) (u : (List (Bool ⊕ ℕ+))) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    prepend (g::u) x = left g (prepend u x) := by
  suffices prepend (g::u) = (left g).comp (prepend u) by
    exact congrArg (fun f : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) => f x) this
  apply Finsupp.lhom_ext
  intro w c
  simp [prepend,left]

theorem cartanPreserves (a : ℂ × ℂ) {x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)} (hx : x ∈ N) : cartan a x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u,v,r,s,rfl⟩ := hy
    induction u with
    | nil =>
      have hp : prepend [] = LinearMap.id := by
        apply Finsupp.lhom_ext
        intro w c
        simp [prepend]
      rw [hp,LinearMap.id_apply,cartan_relation]
      exact Submodule.smul_mem _ _ (by simpa [prepend] using relation_mem r s [] v)
    | cons g u ih =>
      rw [prepend_cons,cartan_left]
      exact Submodule.add_mem _ (leftPreserves g ih)
        (Submodule.smul_mem _ _ (leftPreserves g (relation_mem r s u v)))
  | zero => simp
  | add y z hy hz ihy ihz => simpa only [map_add] using Submodule.add_mem N ihy ihz
  | smul c y hy ih => simpa only [map_smul] using Submodule.smul_mem N c ih

private theorem lowering_relation_mem (r s : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    left (.inr r) (left (.inr s) x) - left (.inr s) (left (.inr r) x) -
      ((s.val : ℂ) - (r.val : ℂ)) • left (.inr (r+s)) x ∈ N := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | single w c =>
    have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
    rw [hs]
    simp only [map_smul,left_basis]
    have hx : relation r s w ∈ N := by simpa [prepend] using relation_mem r s [] w
    convert N.smul_mem c hx using 1
    simp only [relation,smul_sub,smul_smul]
    module
  | add x y hx hy =>
    have hz := Submodule.add_mem N hx hy
    convert hz using 1 <;> simp only [map_add,smul_add] <;> module

private theorem raising_left (i : Bool) (g : (Bool ⊕ ℕ+)) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    raising i (left g x) = left g (raising i x) +
      match g with
      | .inl k => if i=k then cartan (if i then (1,0) else (0,1)) x else 0
      | .inr _ => 0 := by
  cases g with
  | inr r => simpa using raising_mode_commute i r x
  | inl k =>
    let H : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) := if i=k then cartan (if i then (1,0) else (0,1)) else 0
    have hh : (raising i).comp (left (.inl k)) =
        (left (.inl k)).comp (raising i) + H := by
      apply Finsupp.lhom_ext
      intro w c
      have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
      simp only [LinearMap.comp_apply,LinearMap.add_apply,hs,map_smul,left_basis,raising_basis,raisingWord]
      by_cases hik : i=k <;> simp [H,hik,map_smul,smul_add]
    have hh' := LinearMap.congr_fun hh x
    by_cases hik : i=k <;> simpa [H,hik] using hh'

private theorem raising_relation_mem (i : Bool) (r s : ℕ+) (v : (List (Bool ⊕ ℕ+))) :
    raising i (relation r s v) ∈ N := by
  have hh := lowering_relation_mem r s (raising i (basisWord v))
  convert hh using 1
  simp only [relation,map_sub,map_smul]
  repeat' rw [← left_basis]
  simp only [raising_mode_commute]

theorem raisingPreserves (i : Bool) {x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)} (hx : x ∈ N) : raising i x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u,v,r,s,rfl⟩ := hy
    induction u with
    | nil => simpa [prepend] using raising_relation_mem i r s v
    | cons g u ih =>
      rw [prepend_cons,raising_left]
      apply Submodule.add_mem _ (leftPreserves g ih)
      cases g with
      | inr r => exact Submodule.zero_mem _
      | inl k =>
        simp only []
        by_cases hik : i=k
        · simp only [if_pos hik]
          exact cartanPreserves _ (relation_mem r s u v)
        · simp only [if_neg hik]
          exact N.zero_mem
  | zero => simp
  | add y z hy hz ihy ihz => simpa only [map_add] using Submodule.add_mem N ihy ihz
  | smul c y hy ih => simpa only [map_smul] using Submodule.smul_mem N c ih

end D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
namespace D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
noncomputable def negativeIndex (m : ℤ) (hm : m < 0) : ℕ+ :=
  ⟨(-m).toNat,by omega⟩

private theorem negativeIndex_val (m : ℤ) (hm : m < 0) :
    ((negativeIndex m hm).val : ℤ) = -m := by
  simp [negativeIndex,Int.toNat_of_nonneg (by omega : 0 ≤ -m)]

noncomputable def degree : ℂ × ℂ := (-81/8,105/8)
noncomputable def central : ℂ × ℂ := (1,-1)

noncomputable def modeWord (m : ℤ) : (List (Bool ⊕ ℕ+)) → ((List (Bool ⊕ ℕ+)) →₀ ℂ)
  | [] => if hm : m < 0 then basisWord [.inr (negativeIndex m hm)] else 0
  | g::w =>
    if hm : m < 0 then basisWord (.inr (negativeIndex m hm)::g::w)
    else if m = 0 then cartan degree (basisWord (g::w))
    else match g with
      | .inl i => left (.inl i) (modeWord m w)
      | .inr r => left (.inr r) (modeWord m w) +
          ((m+(r.val : ℤ) : ℤ) : ℂ) • modeWord (m-r.val) w +
          if m = r.val then ((m^3-m : ℤ) : ℂ) • cartan central (basisWord w) else 0

noncomputable def mode (m : ℤ) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (modeWord m)

private theorem mode_basis (m : ℤ) (w : (List (Bool ⊕ ℕ+))) : mode m (basisWord w) = modeWord m w := by
  simp [mode,basisWord]

private theorem mode_negative (m : ℤ) (hm : m < 0) :
    mode m = left (.inr (negativeIndex m hm)) := by
  apply Finsupp.lhom_ext
  intro w c
  cases w <;> simp [mode,modeWord,hm,left,basisWord]

private theorem mode_zero : mode 0 = cartan degree := by
  apply Finsupp.lhom_ext
  intro w c
  cases w <;> simp [mode,modeWord,cartan,basisWord,wordWeight]

private theorem mode_positive_left (m : ℤ) (hm : 0 < m) (g : (Bool ⊕ ℕ+)) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    mode m (left g x) = left g (mode m x) +
      match g with
      | .inl _ => 0
      | .inr r => ((m+(r.val : ℤ) : ℤ) : ℂ) • mode (m-r.val) x +
          if m = r.val then ((m^3-m : ℤ) : ℂ) • cartan central x else 0 := by
  let extra : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] ((List (Bool ⊕ ℕ+)) →₀ ℂ) := match g with
    | .inl _ => 0
    | .inr r => ((m+(r.val : ℤ) : ℤ) : ℂ) • mode (m-r.val) +
        if m = r.val then ((m^3-m : ℤ) : ℂ) • cartan central else 0
  have hh : (mode m).comp (left g) = (left g).comp (mode m) + extra := by
    apply Finsupp.lhom_ext
    intro w c
    have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
    simp only [LinearMap.comp_apply,LinearMap.add_apply,hs,map_smul,left_basis,mode_basis]
    cases g with
    | inl i => simp [extra,modeWord,not_lt.mpr (le_of_lt hm),ne_of_gt hm]
    | inr r =>
      have heq : modeWord m (.inr r::w) = left (.inr r) (modeWord m w) +
          ((m+(r.val : ℤ) : ℤ) : ℂ) • modeWord (m-r.val) w +
          if m=r.val then ((m^3-m : ℤ) : ℂ) • cartan central (basisWord w) else 0 := by
        simp [modeWord,not_lt.mpr (le_of_lt hm),ne_of_gt hm]
      rw [heq]
      dsimp only [extra]
      by_cases hmr : m = r.val
      · simp only [if_pos hmr,LinearMap.add_apply,LinearMap.smul_apply,map_smul,mode_basis,cartan_basis]
        module
      · simp only [if_neg hmr,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.zero_apply,
          map_smul,mode_basis,cartan_basis]
        module
  have hh' := LinearMap.congr_fun hh x
  cases g with
  | inl i => simpa [extra] using hh'
  | inr r => by_cases hmr : m=r.val <;> simpa [extra,hmr] using hh'

noncomputable def qleft (g : (Bool ⊕ ℕ+)) : (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) →ₗ[ℂ] (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  N.mapQ N (left g) (by intro x hx; exact leftPreserves g hx)
noncomputable def qcartan (a : ℂ × ℂ) : (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) →ₗ[ℂ] (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  N.mapQ N (cartan a) (by intro x hx; exact cartanPreserves a hx)
private noncomputable def modeProjected (m : ℤ) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) := N.mkQ.comp (mode m)

theorem qleft_project (g : (Bool ⊕ ℕ+)) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    qleft g (N.mkQ x) = N.mkQ (left g x) := rfl

private theorem qcartan_project (a : ℂ × ℂ) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    qcartan a (N.mkQ x) = N.mkQ (cartan a x) := rfl

private theorem qleft_bracket (r s : ℕ+) (y : (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N)) :
    qleft (.inr r) (qleft (.inr s) y) - qleft (.inr s) (qleft (.inr r) y) =
      ((s.val : ℂ)-(r.val : ℂ)) • qleft (.inr (r+s)) y := by
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change qleft (.inr r) (qleft (.inr s) (N.mkQ x)) -
      qleft (.inr s) (qleft (.inr r) (N.mkQ x)) =
      ((s.val : ℂ)-(r.val : ℂ)) • qleft (.inr (r+s)) (N.mkQ x)
    apply sub_eq_zero.mp
    have hx := lowering_relation_mem r s x
    have hz : N.mkQ (left (.inr r) (left (.inr s) x) -
        left (.inr s) (left (.inr r) x) -
        ((s.val : ℂ)-(r.val : ℂ)) • left (.inr (r+s)) x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    simpa only [map_sub,map_smul,← qleft_project] using hz

private theorem qcartan_left (a : ℂ × ℂ) (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    qcartan a (N.mkQ (left (.inr r) x)) =
      qleft (.inr r) (qcartan a (N.mkQ x)) + tokenWeight a (.inr r) • qleft (.inr r) (N.mkQ x) := by
  rw [qcartan_project,cartan_left,map_add,map_smul]
  rfl

private theorem central_left (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    qcartan central (N.mkQ (left (.inr r) x)) = qleft (.inr r) (qcartan central (N.mkQ x)) := by
  rw [qcartan_left]
  simp [tokenWeight,central]

private theorem mode_mixed (m : ℤ) (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    modeProjected m (left (.inr r) x) =
      qleft (.inr r) (modeProjected m x) +
      ((m+(r.val : ℤ) : ℤ) : ℂ) • modeProjected (m-r.val) x +
      if m = r.val then ((m^3-m : ℤ) : ℂ) • qcartan central (N.mkQ x) else 0 := by
  have hr : (0 : ℤ) < r.val := by exact_mod_cast r.pos
  by_cases hm : m < 0
  · have hmr : m-r.val < 0 := by omega
    let q := negativeIndex m hm
    have hq : (q.val : ℤ) = -m := negativeIndex_val m hm
    have hqi : negativeIndex (m-r.val) hmr = q+r := by
      apply PNat.coe_injective
      have hi := negativeIndex_val (m-r.val) hmr
      simp only [PNat.add_coe]
      omega
    have hco : ((m+(r.val : ℤ) : ℤ) : ℂ) = (r.val : ℂ)-(q.val : ℂ) := by
      have hqc : (q.val : ℂ) = -(m : ℂ) := by exact_mod_cast hq
      push_cast
      rw [hqc]
      ring
    change N.mkQ (mode m (left (.inr r) x)) = _
    simp only [modeProjected,LinearMap.comp_apply,mode_negative m hm,mode_negative (m-r.val) hmr,
      hqi,← qleft_project]
    rw [if_neg (by omega),add_zero,hco]
    have hh := qleft_bracket q r (N.mkQ x)
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  · by_cases hm0 : m = 0
    · subst m
      have hmr : (0 : ℤ)-r.val < 0 := by exact Int.sub_neg_of_lt hr
      have hri : negativeIndex (0-r.val) hmr = r := by
        apply PNat.coe_injective
        have hi := negativeIndex_val (0-r.val) hmr
        omega
      simp only [modeProjected,LinearMap.comp_apply,mode_zero,mode_negative (0-r.val) hmr,hri]
      rw [cartan_left,map_add,map_smul,if_neg (by omega),add_zero]
      simp only [← qleft_project,← qcartan_project]
      congr 1
      norm_num [tokenWeight,degree] <;> ring
    · have hp : 0 < m := by omega
      change N.mkQ (mode m (left (.inr r) x)) =
        qleft (.inr r) (N.mkQ (mode m x)) +
        ((m+(r.val : ℤ) : ℤ) : ℂ) • N.mkQ (mode (m-r.val) x) +
        if m = r.val then ((m^3-m : ℤ) : ℂ) • qcartan central (N.mkQ x) else 0
      rw [mode_positive_left m hp]
      simp only [map_add,map_smul,← qleft_project]
      by_cases heq : m = r.val
      · simp only [if_pos heq,map_smul,qcartan_project]
        module
      · simp only [if_neg heq,map_zero]
        module

private theorem mode_relation_zero (m : ℤ) (r s : ℕ+) (v : (List (Bool ⊕ ℕ+))) :
    modeProjected m (relation r s v) = 0 := by
  have hbr := qleft_bracket r s (modeProjected m (basisWord v))
  have hbr' : qleft (.inr r) (qleft (.inr s) (modeProjected m (basisWord v))) =
      qleft (.inr s) (qleft (.inr r) (modeProjected m (basisWord v))) +
      ((s.val : ℂ)-(r.val : ℂ)) • qleft (.inr (r+s)) (modeProjected m (basisWord v)) := by
    exact (sub_eq_iff_eq_add.mp hbr).trans (add_comm _ _)
  have heq1 : m-(r.val : ℤ) = s.val ↔ m = r.val+s.val := by exact Int.sub_eq_iff_eq_add'
  have heq2 : m-(s.val : ℤ) = r.val ↔ m = r.val+s.val := by exact Int.sub_eq_iff_eq_add
  simp only [relation,← left_basis,map_sub,map_smul,mode_mixed,map_add,map_smul,
    central_left]
  rw [hbr']
  simp only [PNat.add_coe,Nat.cast_add,Int.natCast_add,heq1,heq2]
  have hi1 : m-(r.val : ℤ)-(s.val : ℤ) = m-((r+s).val : ℤ) := by simp;omega
  have hi2 : m-(s.val : ℤ)-(r.val : ℤ) = m-((r+s).val : ℤ) := by simp;omega
  simp only [hi1,hi2]
  have hrpos : (0 : ℤ) < r.val := by exact_mod_cast r.pos
  have hspos : (0 : ℤ) < s.val := by exact_mod_cast s.pos
  split_ifs <;> try omega
  all_goals simp only [map_smul,map_add,map_sub,map_zero,smul_zero,zero_smul,add_zero,zero_add,
    PNat.add_coe,Int.natCast_add]
  all_goals subst_vars
  all_goals push_cast
  all_goals module

theorem modePreserves (m : ℤ) {x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)} (hx : x ∈ N) : mode m x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u,v,r,s,rfl⟩ := hy
    have hu (u : (List (Bool ⊕ ℕ+))) : ∀ m : ℤ, mode m (prepend u (relation r s v)) ∈ N := by
      induction u with
      | nil =>
        intro m
        have hh := mode_relation_zero m r s v
        change N.mkQ (mode m (relation r s v)) = 0 at hh
        have hh' := (Submodule.Quotient.mk_eq_zero _).mp hh
        simpa [prepend] using hh'
      | cons g u ih =>
        intro m
        by_cases hm : m < 0
        · rw [mode_negative m hm]
          exact leftPreserves _ (relation_mem r s (g::u) v)
        · by_cases hm0 : m = 0
          · rw [hm0,mode_zero]
            exact cartanPreserves _ (relation_mem r s (g::u) v)
          · rw [prepend_cons,mode_positive_left m (by omega)]
            apply Submodule.add_mem _ (leftPreserves g (ih m))
            cases g with
            | inl i => exact N.zero_mem
            | inr r' =>
              simp only []
              apply Submodule.add_mem _ (N.smul_mem _ (ih (m-r'.val)))
              split_ifs
              · exact N.smul_mem _ (cartanPreserves _ (relation_mem r s u v))
              · exact N.zero_mem
    exact hu u m
  | zero => simp
  | add x y hx hy ih ih' => simpa only [map_add] using N.add_mem ih ih'
  | smul c x hx ih => simpa only [map_smul] using N.smul_mem c ih

private theorem modeWord_eigen (a : ℂ × ℂ) (w : (List (Bool ⊕ ℕ+))) (m : ℤ) :
    cartan a (modeWord m w) =
      (wordWeight a w - (m : ℂ)/3*(a.1+a.2)) • modeWord m w := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m < 0
    · have heq : modeWord m [] = basisWord [.inr (negativeIndex m hm)] := by simp [modeWord,hm]
      rw [heq,cartan_basis]
      have hi := negativeIndex_val m hm
      have hic : ((negativeIndex m hm).val : ℂ) = -(m : ℂ) := by exact_mod_cast hi
      simp [wordWeight,tokenWeight,hic]
      module
    · simp [modeWord,hm]
  | cons g w ih =>
    by_cases hm : m < 0
    · have heq : modeWord m (g::w) = basisWord (.inr (negativeIndex m hm)::g::w) := by simp [modeWord,hm]
      rw [heq,cartan_basis]
      have hi := negativeIndex_val m hm
      have hic : ((negativeIndex m hm).val : ℂ) = -(m : ℂ) := by exact_mod_cast hi
      simp [wordWeight,tokenWeight,hic]
      module
    · by_cases hm0 : m = 0
      · subst m
        simp [modeWord,cartan_basis,map_smul,wordWeight]
        module
      · cases g with
        | inl i =>
          have heq : modeWord m (.inl i::w) = left (.inl i) (modeWord m w) := by simp [modeWord,hm,hm0]
          rw [heq,cartan_left,ih]
          simp only [wordWeight,List.map_cons,List.sum_cons,map_smul]
          module
        | inr r =>
          have heq : modeWord m (.inr r::w) = left (.inr r) (modeWord m w) +
              ((m+(r.val : ℤ) : ℤ) : ℂ) • modeWord (m-r.val) w +
              if m=r.val then ((m^3-m : ℤ) : ℂ) • cartan central (basisWord w) else 0 := by
            simp [modeWord,hm,hm0]
          rw [heq]
          by_cases hmr : m = r.val <;>
            simp only [hmr,ite_true,ite_false,map_add,map_smul,cartan_left,ih,cartan_basis]
          · simp [wordWeight,tokenWeight,hmr,map_smul]
            push_cast
            module
          · simp [wordWeight,tokenWeight,map_smul]
            push_cast
            module

private theorem raisingWord_eigen (a : ℂ × ℂ) (i : Bool) (w : (List (Bool ⊕ ℕ+))) :
    cartan a (raisingWord i w) =
      (wordWeight a w-tokenWeight a (.inl i)) • raisingWord i w := by
  induction w with
  | nil => simp [raisingWord]
  | cons g w ih =>
    cases g with
    | inr r =>
      simp only [raisingWord,cartan_left,ih]
      simp only [wordWeight,List.map_cons,List.sum_cons,map_smul]
      module
    | inl k =>
      simp only [raisingWord]
      by_cases hik : i = k
      · subst k
        simp only [ite_true,map_add,cartan_left,ih,cartan_basis,map_smul]
        simp only [wordWeight,List.map_cons,List.sum_cons,map_smul]
        module
      · simp only [if_neg hik,add_zero,cartan_left,ih]
        simp only [wordWeight,List.map_cons,List.sum_cons,map_smul]
        module

private theorem cartan_mode (a : ℂ × ℂ) (m : ℤ) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    cartan a (mode m x)-mode m (cartan a x) =
      (-(m : ℂ)/3*(a.1+a.2)) • mode m x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | single w c =>
    have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
    rw [hs]
    simp only [map_smul,cartan_basis,mode_basis,modeWord_eigen]
    module
  | add x y hx hy =>
    simp only [map_add,smul_add]
    have hh := congrArg₂ (· + ·) hx hy
    convert hh using 1 <;> module

noncomputable def qmode (m : ℤ) : Module.End ℂ (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  N.mapQ N (mode m) (by intro x hx;exact modePreserves m hx)

theorem qcartan_mode (a : ℂ × ℂ) (m : ℤ) :
    ⁅qcartan a,qmode m⁆ = (-(m : ℂ)/3*(a.1+a.2)) • qmode m := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    have hh := congrArg N.mkQ (cartan_mode a m x)
    change N.mkQ (cartan a (mode m x))-N.mkQ (mode m (cartan a x)) =
      (-(m : ℂ)/3*(a.1+a.2)) • N.mkQ (mode m x)
    simpa only [map_sub,map_smul] using hh

private theorem qmode_mixed (m : ℤ) (r : ℕ+) :
    ⁅qmode m,qleft (.inr r)⁆ =
      ((m+(r.val : ℤ) : ℤ) : ℂ) • qmode (m-r.val) +
      if m = r.val then ((m^3-m : ℤ) : ℂ) • qcartan central else 0 := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    by_cases hmr : m = r.val
    · rw [if_pos hmr]
      change N.mkQ (mode m (left (.inr r) x)) - N.mkQ (left (.inr r) (mode m x)) =
        ((m+(r.val : ℤ) : ℤ) : ℂ) • N.mkQ (mode (m-r.val) x) +
        ((m^3-m : ℤ) : ℂ) • N.mkQ (cartan central x)
      have hh := mode_mixed m r x
      rw [if_pos hmr] at hh
      change N.mkQ (mode m (left (.inr r) x)) =
        N.mkQ (left (.inr r) (mode m x)) +
        ((m+(r.val : ℤ) : ℤ) : ℂ) • N.mkQ (mode (m-r.val) x) +
        ((m^3-m : ℤ) : ℂ) • N.mkQ (cartan central x) at hh
      rw [hh]
      module
    · rw [if_neg hmr,add_zero]
      change N.mkQ (mode m (left (.inr r) x)) - N.mkQ (left (.inr r) (mode m x)) =
        ((m+(r.val : ℤ) : ℤ) : ℂ) • N.mkQ (mode (m-r.val) x)
      have hh := mode_mixed m r x
      rw [if_neg hmr,add_zero] at hh
      change N.mkQ (mode m (left (.inr r) x)) =
        N.mkQ (left (.inr r) (mode m x)) +
        ((m+(r.val : ℤ) : ℤ) : ℂ) • N.mkQ (mode (m-r.val) x) at hh
      rw [hh]
      module

theorem qmode_negative (r : ℕ+) : qmode (-(r.val : ℤ)) = qleft (.inr r) := by
  have hr : -(r.val : ℤ) < 0 := by have := r.pos;omega
  have hri : negativeIndex (-(r.val : ℤ)) hr = r := by
    apply PNat.coe_injective
    have hi := negativeIndex_val (-(r.val : ℤ)) hr
    omega
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (mode (-(r.val : ℤ)) x) = N.mkQ (left (.inr r) x)
    rw [mode_negative _ hr,hri]

theorem qmode_zero : qmode 0 = qcartan degree := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (mode 0 x) = N.mkQ (cartan degree x)
    rw [mode_zero]

private theorem qmode_zero_bracket (m : ℤ) : ⁅qmode m,qmode 0⁆ = (m : ℂ) • qmode m := by
  rw [qmode_zero,← lie_skew,qcartan_mode]
  norm_num [degree]

private theorem qmode_central_bracket (m : ℤ) : ⁅qmode m,qcartan central⁆ = 0 := by
  rw [← lie_skew,qcartan_mode]
  norm_num [central]

theorem qmode_positive_root (m : ℤ) (hm : 0 < m) (i : Bool) :
    ⁅qmode m,qleft (.inl i)⁆ = 0 := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (mode m (left (.inl i) x)) - N.mkQ (left (.inl i) (mode m x)) = 0
    rw [mode_positive_left m hm]
    simp

noncomputable def qvacuum : (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) := N.mkQ (basisWord [])

private theorem qmode_positive_vacuum (m : ℤ) (hm : 0 < m) : qmode m qvacuum = 0 := by
  change N.mkQ (mode m (basisWord [])) = 0
  rw [mode_basis]
  simp [modeWord,not_lt.mpr (le_of_lt hm)]

private theorem qwordVector (w : (List (Bool ⊕ ℕ+))) :
    D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.wordVector qleft qvacuum w = N.mkQ (basisWord w) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.wordVector,ih,qleft_project,left_basis]

private theorem qword_span :
    Submodule.span ℂ (Set.range (D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.wordVector qleft qvacuum)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ x ∈ _
    induction x using Finsupp.induction_linear with
    | zero => simp
    | single w c =>
      have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
      rw [hs,map_smul,← qwordVector]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨w,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

private theorem qmode_positive_brackets (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    ⁅qmode m,qmode n⁆ = ((m-n : ℤ) : ℂ) • qmode (m+n) := by
  apply D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.positive_brackets_from_mixed qleft qvacuum qword_span qmode
    (qcartan central) qmode_negative qmode_positive_root
    (fun m r => by rw [qmode_negative];exact qmode_mixed m r)
    qmode_zero_bracket qmode_central_bracket qmode_positive_vacuum m n hm hn


theorem qmode_virasoro (m n : ℤ) :
    ⁅qmode m,qmode n⁆ = ((m-n : ℤ) : ℂ) • qmode (m+n) +
      if m = -n then ((m^3-m : ℤ) : ℂ) • qcartan central else 0 := by
  exact D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.full_brackets_from_mixed qmode (qcartan central)
    (fun m r => by rw [qmode_negative];exact qmode_mixed m r)
    qmode_zero_bracket qmode_positive_brackets m n


end D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction

namespace D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction

private theorem wordWeight_add (a b : ℂ × ℂ) (w : (List (Bool ⊕ ℕ+))) :
    wordWeight (a+b) w = wordWeight a w + wordWeight b w := by
  induction w with
  | nil => simp [wordWeight]
  | cons g w ih =>
    simp only [wordWeight,List.map_cons,List.sum_cons] at ih ⊢
    cases g with
    | inl i => cases i <;> simp [tokenWeight,ih] <;> ring
    | inr r => simp [tokenWeight,ih];ring

private theorem wordWeight_smul (c : ℂ) (a : ℂ × ℂ) (w : (List (Bool ⊕ ℕ+))) :
    wordWeight (c • a) w = c * wordWeight a w := by
  induction w with
  | nil => simp [wordWeight]
  | cons g w ih =>
    simp only [wordWeight,List.map_cons,List.sum_cons] at ih ⊢
    cases g with
    | inl i => cases i <;> simp [tokenWeight,ih] <;> ring
    | inr r => simp [tokenWeight,ih];ring

private theorem cartan_add (a b : ℂ × ℂ) : cartan (a+b) = cartan a + cartan b := by
  apply Finsupp.lhom_ext
  intro w c
  have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
  simp only [hs,map_smul,LinearMap.add_apply,cartan_basis,wordWeight_add,add_smul,smul_add]

private theorem cartan_smul (c : ℂ) (a : ℂ × ℂ) : cartan (c • a) = c • cartan a := by
  apply Finsupp.lhom_ext
  intro w d
  have hs : Finsupp.single w d = d • basisWord w := by simp [basisWord]
  simp only [hs,map_smul,LinearMap.smul_apply,cartan_basis,wordWeight_smul,smul_smul] <;> module

private theorem cartan_commute (a b : ℂ × ℂ) :
    (cartan a).comp (cartan b) = (cartan b).comp (cartan a) := by
  apply Finsupp.lhom_ext
  intro w c
  have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
  simp only [hs,LinearMap.comp_apply,map_smul,cartan_basis]
  module

private theorem cartan_raising (a : ℂ × ℂ) (i : Bool) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    cartan a (raising i x)-raising i (cartan a x) =
      -tokenWeight a (.inl i) • raising i x := by
  have hh : (cartan a).comp (raising i)-(raising i).comp (cartan a) =
      -tokenWeight a (.inl i) • raising i := by
    apply Finsupp.lhom_ext
    intro w c
    have hs : Finsupp.single w c = c • basisWord w := by simp [basisWord]
    simp only [hs,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,map_smul,
      cartan_basis,raising_basis,raisingWord_eigen]
    module
  exact LinearMap.congr_fun hh x

noncomputable def qraising (i : Bool) : Module.End ℂ (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  N.mapQ N (raising i) (by intro x hx;exact raisingPreserves i hx)

theorem qcartan_add (a b : ℂ × ℂ) : qcartan (a+b) = qcartan a + qcartan b := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (cartan (a+b) x) = N.mkQ (cartan a x)+N.mkQ (cartan b x)
    rw [cartan_add,LinearMap.add_apply,map_add]

theorem qcartan_smul (c : ℂ) (a : ℂ × ℂ) : qcartan (c • a) = c • qcartan a := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (cartan (c • a) x) = c • N.mkQ (cartan a x)
    rw [cartan_smul,LinearMap.smul_apply,map_smul]

theorem qcartan_commute (a b : ℂ × ℂ) : ⁅qcartan a,qcartan b⁆ = 0 := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (cartan a (cartan b x))-N.mkQ (cartan b (cartan a x)) = 0
    have hh := LinearMap.congr_fun (cartan_commute a b) x
    change cartan a (cartan b x) = cartan b (cartan a x) at hh
    rw [hh,sub_self]

theorem qcartan_qleft (a : ℂ × ℂ) (g : (Bool ⊕ ℕ+)) :
    ⁅qcartan a,qleft g⁆ = tokenWeight a g • qleft g := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (cartan a (left g x))-N.mkQ (left g (cartan a x)) =
      tokenWeight a g • N.mkQ (left g x)
    rw [cartan_left,map_add,map_smul]
    module

theorem qcartan_qraising (a : ℂ × ℂ) (i : Bool) :
    ⁅qcartan a,qraising i⁆ = -tokenWeight a (.inl i) • qraising i := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    have hh := congrArg N.mkQ (cartan_raising a i x)
    change N.mkQ (cartan a (raising i x))-N.mkQ (raising i (cartan a x)) =
      -tokenWeight a (.inl i) • N.mkQ (raising i x)
    simpa only [map_sub,map_smul] using hh

theorem qraising_qleft (i : Bool) (g : (Bool ⊕ ℕ+)) :
    ⁅qraising i,qleft g⁆ = match g with
      | .inl k => if i=k then qcartan (if i then (1,0) else (0,1)) else 0
      | .inr _ => 0 := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    change N.mkQ (raising i (left g x))-N.mkQ (left g (raising i x)) = _
    rw [raising_left,map_add]
    cases g with
    | inl k => by_cases hik : i=k <;> simp [hik,qcartan_project] <;> rfl
    | inr r => simp

theorem qraising_negative (i : Bool) (n : ℤ) (hn : n < 0) :
    ⁅qraising i,qmode n⁆ = 0 := by
  have hr : -(n : ℤ) > 0 := by exact Int.neg_pos_of_neg hn
  let r := negativeIndex n hn
  have hh := qmode_negative r
  have hi : -(r.val : ℤ) = n := by have := negativeIndex_val n hn;dsimp [r];omega
  rw [hi] at hh
  rw [hh,qraising_qleft]

end D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
