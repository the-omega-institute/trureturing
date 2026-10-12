/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnClassWidth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnClassWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnBlockFactorization
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISupportedFixedCycleClassWord
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnipotentDuality
import Mathlib.Data.List.OfFn

/-! Constructive uniform class PRODUCT width for the actual fixed long-cycle
qth power. The elementary12-word is consumed on6480 genuine small supported
upper factors, then the accepted25 upper/lower width. Original PartII Section5
uses LS2; this module proves the needed type-A large-rank width directly.
No class-product coverage or width oracle is a premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace NikolovSegal.PartIISLnClassWidth
open Matrix PartIIUnitriangularLayers PartIIFixedSLnPower PartIISLnBlockFactorization
universe u
variable {F : Type u} [Field F]

private def flatten {S : Type*} {m n : ℕ} (a : Fin m → Fin n → S) : Fin (m*n) → S :=
  fun i => a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
private theorem ordered_flatten {S : Type*} [Group S] {m n : ℕ}
    (a : Fin m → Fin n → S) :
    orderedProduct (flatten a)=orderedProduct (fun i => orderedProduct (a i)) := by
  unfold orderedProduct
  rw [List.ofFn_mul,List.prod_flatten,List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_def]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ac_rfl
  simp only [flatten,he,Equiv.symm_apply_apply]
private theorem ordered_append {S : Type*} [Group S] {m n : ℕ}
    (a : Fin m → S) (b : Fin n → S) :
    orderedProduct (Fin.append a b)=orderedProduct a*orderedProduct b := by
  simp only [orderedProduct,List.ofFn_fin_append,List.prod_append]

/-- Every upper target, over every field, is an exact77760-word in the
SAME fixed q-power class. All6480 support slots (including identities) are
constructed from the actual80 consecutive coordinate chunks. -/
theorem actual_fixed_cycle_upper_full_class_word (q r k : ℕ)
    (hp : k+2≤q*r) (hL : 16≤q*r+1)
    (u : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (hu : LayerDepth 1 (u.val-1)) :
    ∃ c : Fin ((80+80*80)*12) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i)=u := by
  classical
  let s := (q*r+1)/8
  obtain ⟨hs,hN,hd⟩ := actual_long_cycle_chunk_bounds q r k hp hL
  obtain ⟨T,U,a,b,hT,hU,ha,hb,hda,hdb,hprod⟩ :=
    actual_upper_eighty_chunk_factorization s hs hN u hu
  have hT' : ∀ i, (T i).ncard≤2*s := by
    intro i
    rw [← Nat.card_coe_set_eq]
    have hh := hT i
    omega
  have hU' : ∀ i j, (U i j).ncard≤2*s := by
    intro i j
    rw [← Nat.card_coe_set_eq]
    exact hU i j
  choose ca hca using fun i =>
    PartIISupportedClassTransport.actual_fixed_cycle_set_supported_upper_class_word
      q r k (2*s) hd (T i) (hT' i) (a i) (hda i) (ha i)
  choose cb hcb using fun i j =>
    PartIISupportedClassTransport.actual_fixed_cycle_set_supported_upper_class_word
      q r k (2*s) hd (U i j) (hU' i j) (b i j) (hdb i j) (hb i j)
  let rows : Fin (80+80*80) → Fin 12 → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F :=
    Fin.append ca (flatten cb)
  refine ⟨flatten rows,?_⟩
  have he : (fun i => (flatten rows i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*flatten rows i)=
      flatten (fun i j => (rows i j)⁻¹*(fixedElement (F:=F) (q*r) k)^q*rows i j) := rfl
  rw [he,ordered_flatten]
  have hr : (fun i => orderedProduct (fun j => (rows i j)⁻¹*(fixedElement (F:=F) (q*r) k)^q*rows i j))=
      Fin.append a (flatten b) := by
    apply funext
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro t
      simpa only [rows,Fin.append_left] using hca t
    · intro t
      simpa only [rows,Fin.append_right,flatten] using
        hcb (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  rw [hr,ordered_append,ordered_flatten]
  exact hprod

private theorem dual_fixed (q r k : ℕ) :
    PartIIUnipotentDuality.dual (fixedElement (F:=F) (q*r) k)=fixedElement (q*r) k := by
  apply SpecialLinearGroup.ext
  intro i j
  change (fixedElement (F:=F) (q*r) k)⁻¹ j i=fixedElement (q*r) k i j
  rw [fixedElement,(cycleClass% slPerm_inv)]
  change (cycleClass% pMatrix) ((cycleClass% paired) (q*r) k)⁻¹ j i=
    (cycleClass% pMatrix) ((cycleClass% paired) (q*r) k) i j
  rw [(cycleClass% pMatrix_entry),(cycleClass% pMatrix_entry)]
  congr 1
  exact propext (((cycleClass% paired) (q*r) k).symm_apply_eq.trans eq_comm)

/-- Lower targets use the genuine inverse-transpose automorphism, which
FIXES the constructed permutation matrix. The conjugacy class is unchanged. -/
theorem actual_fixed_cycle_lower_full_class_word (q r k : ℕ)
    (hp : k+2≤q*r) (hL : 16≤q*r+1)
    (u : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (hu : SLnUnipotentWidth.Lower u) :
    ∃ c : Fin ((80+80*80)*12) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i)=u := by
  let dual := PartIIUnipotentDuality.dual (F:=F) (n:=k+4*(q*r+1)+2)
  obtain ⟨c,hc⟩ := actual_fixed_cycle_upper_full_class_word q r k hp hL
    (dual u) (PartIIUnipotentDuality.actual_dual_lower_target u hu)
  refine ⟨fun i => dual (c i),?_⟩
  have hm := map_list_prod dual.toMonoidHom
    (List.ofFn (fun i => (c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i))
  change dual (orderedProduct (fun i => (c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i))=_ at hm
  have hinv : dual (dual u)=u := PartIIUnipotentDuality.dual.left_inv u
  rw [hc,hinv] at hm
  simp only [List.map_ofFn,Function.comp_def] at hm
  change u=orderedProduct (fun i => dual ((c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i)) at hm
  have hfix : dual ((fixedElement (F:=F) (q*r) k)^q)=(fixedElement (q*r) k)^q := by
    rw [map_pow]
    exact congrArg (fun t => t^q) (dual_fixed q r k)
  have hf : (fun i => dual ((c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i))=
      fun i => (dual (c i))⁻¹*(fixedElement (F:=F) (q*r) k)^q*dual (c i) := by
    funext i
    simp only [map_mul,map_inv,hfix]
  rw [hf] at hm
  exact hm.symm

/-- Full actual SLn class coverage at ONE absolute positive length1944000,
independent of field, rank, q and target. No finite-field assumption.
The same fixed matrix supplies all25 genuine alternating unipotent slots. -/
theorem actual_fixed_cycle_full_group_class_word (q r k : ℕ)
    (hp : k+2≤q*r) (hL : 16≤q*r+1)
    (g : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F) :
    ∃ c : Fin (25*((80+80*80)*12)) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (c i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i)=g := by
  classical
  obtain ⟨u,hu,hprod⟩ := SLnUnipotentWidth.alternating_unipotent_25 _ g
  have hw : ∀ i, ∃ c : Fin ((80+80*80)*12) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun j => (c j)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c j)=u i := by
    intro i
    have hh := hu i
    by_cases he : i.val%2=0
    · rw [if_pos he] at hh
      apply actual_fixed_cycle_upper_full_class_word q r k hp hL (u i)
      intro a b hab
      simp only [Matrix.sub_apply,hh a b hab,sub_self]
    · rw [if_neg he] at hh
      exact actual_fixed_cycle_lower_full_class_word q r k hp hL (u i)
        ((SLnUnipotentWidth.lower_iff_literal _).mpr hh)
  choose c hc using hw
  refine ⟨flatten c,?_⟩
  change orderedProduct (flatten (fun i j => (c i j)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i j))=g
  rw [ordered_flatten,show (fun i => orderedProduct (fun j => (c i j)⁻¹*(fixedElement (F:=F) (q*r) k)^q*c i j))=u from funext hc]
  exact hprod
end NikolovSegal.PartIISLnClassWidth
