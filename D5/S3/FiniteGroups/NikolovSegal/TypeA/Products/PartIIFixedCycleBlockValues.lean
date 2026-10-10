/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIFixedCycleBlockValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnDisplacedClassWords
import Mathlib.Data.Nat.ModEq

/-! Concrete long-cycle consumption of the elementary displacement proof.
The injection consists of EVEN powers along the genuine q-powered cycle;
its image and the next (odd) powers are disjoint by qr+1 coprime to q.
Original arbitrary bare PSLn/divisor tuples then consume the actual class
word. The fixed correction precedes ALL block targets. This proves a
local shifted VALUE range, not the still-missing full class PRODUCT width. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIFixedCycleBlockValues
open Matrix Equiv PartIISLnDisplacedClassWords PartIIFixedSLnPower
universe u
variable {F : Type u} [Field F]

private theorem residue_injective (q r x y : ℕ) (hx : x < q*r+1) (hy : y < q*r+1)
    (h : (q*x)%(q*r+1)=(q*y)%(q*r+1)) : x=y := by
  have hco : Nat.Coprime (q*r+1) q := by
    apply Nat.Coprime.symm
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right q
  have hm : Nat.ModEq (q*r+1) (q*x) (q*y) := h
  have hm' := hm.cancel_left_div_gcd (by omega)
  rw [hco.gcd_eq_one,Nat.div_one] at hm'
  exact hm'.eq_of_lt_of_lt hx hy

/-- The actual 2d-coordinate block sits on even powers in ONE selected
long cycle of the constructed fixed matrix. No abstract cycle law is input. -/
noncomputable def actualCycleEmbedding (q r k d : ℕ) (hd : 4*d≤q*r+1) :
    (Fin d ⊕ Fin d) ↪ Fin (k+4*(q*r+1)+2) where
  toFun x := (cycleClass% leftIndex) (q*r+1) k
    ⟨(q*(2*(finSumFinEquiv x).val))%(q*r+1),Nat.mod_lt _ (by omega)⟩
  inj' := by
    intro x y hxy
    have he := ((cycleClass% leftIndex) (q*r+1) k).injective hxy
    have hv := congrArg Fin.val he
    have hx := (finSumFinEquiv x).isLt
    have hy := (finSumFinEquiv y).isLt
    have hv' := residue_injective q r (2*(finSumFinEquiv x).val)
      (2*(finSumFinEquiv y).val) (by omega) (by omega) hv
    apply (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).injective
    apply Fin.ext
    omega

private theorem actual_cycle_displacement (q r k d : ℕ) (hd : 4*d≤q*r+1)
    (x y : Fin d ⊕ Fin d) :
    (((cycleClass% paired) (q*r) k)^q) (actualCycleEmbedding q r k d hd x)≠
      actualCycleEmbedding q r k d hd y := by
  intro he
  change (((cycleClass% paired) (q*r) k)^q)
    ((cycleClass% leftIndex) (q*r+1) k
      ⟨(q*(2*(finSumFinEquiv x).val))%(q*r+1),_⟩)=
      (cycleClass% leftIndex) (q*r+1) k
        ⟨(q*(2*(finSumFinEquiv y).val))%(q*r+1),_⟩ at he
  rw [(cycleClass% paired_power_left),(cycleClass% cycle_power)] at he
  have hh := ((cycleClass% leftIndex) (q*r+1) k).injective he
  have hv := congrArg Fin.val hh
  change ((q*(2*(finSumFinEquiv x).val))%(q*r+1)+q%(q*r+1))%(q*r+1)=
      (q*(2*(finSumFinEquiv y).val))%(q*r+1) at hv
  have hv' : (q*(2*(finSumFinEquiv x).val+1))%(q*r+1)=
      (q*(2*(finSumFinEquiv y).val))%(q*r+1) := by
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_mod_mod,Nat.mod_add_mod] using hv
  have hx := (finSumFinEquiv x).isLt
  have hy := (finSumFinEquiv y).isLt
  have hh' := residue_injective q r (2*(finSumFinEquiv x).val+1)
    (2*(finSumFinEquiv y).val) (by omega) (by omega) hv'
  omega

private theorem paired_first (p k : ℕ) : (cycleClass% paired) p k 0=0 := by
  change ((cycleClass% leftCycle) p k) (((cycleClass% reflected) p k) 0)=0
  rw [(cycleClass% reflected_fix_left) p k 0 (by simp)]
  change ((finCycle (1:Fin (p+1))).viaEmbedding ((cycleClass% leftIndex) (p+1) k)) 0=0
  apply Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  change 2*j.val+1=0 at hh
  omega
private theorem powered_first (p k t : ℕ) : (((cycleClass% paired) p k)^t) 0=0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [pow_succ',Perm.mul_apply,ih,paired_first]

/-- Genuine TWELVE-factor class-word reconstruction on the concrete
long-cycle block, with no displacement/cycle/class-width hypothesis left. -/
theorem actual_fixed_cycle_upper_class_word (q r k d : ℕ) (hd : 4*d≤q*r+1)
    (u : SpecialLinearGroup (Fin d) F)
    (hu : PartIIUnitriangularLayers.LayerDepth 1 (u.val-1)) :
    ∃ a : Fin 12 → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (a i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*a i)=
        padAlong (actualCycleEmbedding q r k d hd)
          (PartIISLnUnipotentCommutators.doubleEmbed u) := by
  rw [(cycleClass% fixed_pow)]
  exact actual_displaced_upper_twelve_class_factors
    (((cycleClass% paired) (q*r) k)^q)
    (by rw [map_pow,(cycleClass% paired_sign),one_pow]) 0 (powered_first (q*r) k q)
    (actualCycleEmbedding q r k d hd) (actual_cycle_displacement q r k d hd) u hu

/-- Original arbitrary bare projective actions and q/e, with ONE global
correction before every genuine block target. The exact shifted target is
retained; full-group/uniform class width is not assumed or asserted. -/
theorem actual_bare_PSLn_fixed_cycle_block_values [Fintype F]
    (q : ℕ) (hq : 0 < q) (r k K d : ℕ) (hp : k+2≤q*r)
    (hd : 4*d≤q*r+1) (h2 : 2<Fintype.card F) (hF : Fintype.card F≤K)
    (beta : Fin (12*(K^2*(K^K*2))) →
      MulAut (ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (12*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    let pi := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    let z := pi (fixedElement (F:=F) (q*r) k)
    ∃ y : Fin (12*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ u : SpecialLinearGroup (Fin d) F,
        PartIIUnitriangularLayers.LayerDepth 1 (u.val-1) →
        ∃ c : Fin (12*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
            pi (padAlong (actualCycleEmbedding q r k d hd)
              (PartIISLnUnipotentCommutators.doubleEmbed u))*((z^q)^12)⁻¹ := by
  classical
  dsimp only
  let pi := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
  obtain ⟨_,y,hy⟩ := PartIIConjugacyValueConsumption.actual_bare_PSLn_conjugacy_word_values
    q hq r k K 12 hp h2 hF beta e he
  refine ⟨y,?_⟩
  intro u hu
  obtain ⟨a,ha⟩ := actual_fixed_cycle_upper_class_word q r k d hd u hu
  obtain ⟨c,hc⟩ := hy (fun i => pi (a i))
  refine ⟨c,?_⟩
  have hmap := map_list_prod pi
    (List.ofFn (fun i => (a i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*a i))
  change pi (orderedProduct (fun i => (a i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*a i))=_ at hmap
  rw [ha] at hmap
  have hword : orderedProduct (fun i => (pi (a i))⁻¹*(pi (fixedElement (q*r) k))^q*pi (a i))=
      pi (padAlong (actualCycleEmbedding q r k d hd)
        (PartIISLnUnipotentCommutators.doubleEmbed u)) := by
    simpa only [orderedProduct,List.map_ofFn,Function.comp_def,map_mul,map_inv,map_pow] using hmap.symm
  exact hc.trans (congrArg (fun w => w*((pi (fixedElement (q*r) k)^q)^12)⁻¹) hword)
end NikolovSegal.PartIIFixedCycleBlockValues
