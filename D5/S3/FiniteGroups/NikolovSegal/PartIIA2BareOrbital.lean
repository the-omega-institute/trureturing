/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2BareOrbital
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2BareOrbital
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2RootSeparation
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2GraphReconstruction
/-! Nikolov--Segal Part II sections 2 and 6, Proposition 6.2 and the A2
orbital case on pp260--261. Bare-auto root images/common field law are
derived from actual geometry. The proved field/graph inputs and genuine
height-one/central reconstruction supply the orbital PRODUCT. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "a2Actual%" id:ident : term => do
  let env ← getEnv
  let owner := if id.getId == `root_additive_coordinates then "PartIIA2RootNormalization"
    else "PartIIA2GraphReconstruction"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let chosen := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match chosen with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved A2 actual kernel {id} from {owner} not found"
namespace NikolovSegal.PartIIA2BareOrbital
open PartIIA2Orbital PartIIA2RootNormalization PartIIA2GraphSupply
open PartIIA2RootSeparation PartIIA2GraphTorus Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev rt (r : Fin 3) (t : F) : SL(3,F) := (a2Kernel% root) r t
private def swapRoot : Fin 3 → Fin 3 := ![1,0,2]

private theorem tau_rt (r : Fin 3) (t : F) : tau (rt r t)=rt (swapRoot r) (-t) := by
  fin_cases r
  · exact tau_T01 t
  · exact tau_T12 t
  · exact tau_T02 t

private theorem tau_root_image (r : Fin 3) :
    (positiveRoot (F := F) r).map tau.toMonoidHom=positiveRoot (swapRoot r) := by
  have hle : (positiveRoot (F := F) r).map tau.toMonoidHom ≤ positiveRoot (swapRoot r) := by
    rintro g ⟨z,⟨t,rfl⟩,rfl⟩
    exact ⟨-t,(tau_rt r t).symm⟩
  apply le_antisymm hle
  rintro g ⟨t,rfl⟩
  refine ⟨rt r (-t),⟨-t,rfl⟩,?_⟩
  change tau (rt r (-t))=rt (swapRoot r) t
  simpa only [neg_neg] using tau_rt r (-t)

private theorem root_preserving_U_model (nu : MulAut SL(3,F))
    (hroot : ∀ r, (positiveRoot r).map nu.toMonoidHom=positiveRoot (F := F) r) :
    ∃ (a : Fin 3 → Fˣ) (phi : RingAut F), ∀ z ∈ upperUnipotent (F := F),
      nu z=diagonalFieldAut a phi z := by
  classical
  choose f hf using fun r => (a2Actual% root_additive_coordinates) nu r (hroot r)
  obtain ⟨phi,h0,h1,h2⟩ := actual_positive_root_field nu f hf
  have hc0 : f 0 1 ≠ 0 := by intro h; exact one_ne_zero ((f 0).map_eq_zero_iff.mp h)
  have hc1 : f 1 1 ≠ 0 := by intro h; exact one_ne_zero ((f 1).map_eq_zero_iff.mp h)
  let u0 : Fˣ := Units.mk0 (f 0 1) hc0
  let u1 : Fˣ := Units.mk0 (f 1 1) hc1
  let a : Fin 3 → Fˣ := ![u0*u1,u1,1]
  have hf' : ∀ r t, nu (rt r t)=rt r (f r t) := by
    intro r t; exact hf r t
  have hr : ∀ r t, nu (rt r t)=diagonalFieldAut a phi (rt r t) := by
    intro r t
    rw [hf' r]
    change rt r (f r t)=diagonalFieldAut a phi (rt r t)
    change transvection ((a2Kernel% root_ne) r) (f r t)=
      diagonalFieldAut a phi (transvection ((a2Kernel% root_ne) r) t)
    rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    apply congrArg (transvection ((a2Kernel% root_ne) r))
    fin_cases r
    · change f 0 t=(↑(u0*u1):F)*(↑u1:F)⁻¹*phi t
      rw [h0]
      simp [a,u0,u1,Units.val_mul,mul_assoc,hc1]
    · change f 1 t=(↑u1:F)*(↑((1:Fˣ)⁻¹):F)*phi t
      rw [h1]
      simp [a,u1]
    · change f 2 t=(↑(u0*u1):F)*(↑((1:Fˣ)⁻¹):F)*phi t
      rw [h2]
      simp [a,u0,u1,Units.val_mul]
  refine ⟨a,phi,?_⟩
  rintro z ⟨A,B,C,rfl⟩
  rw [← (a2Kernel% three_root_product) A B C]
  simp only [map_mul]
  change nu (rt 0 A)*nu (rt 1 B)*nu (rt 2 (C-A*B))=
    diagonalFieldAut a phi (rt 0 A)*diagonalFieldAut a phi (rt 1 B)*
      diagonalFieldAut a phi (rt 2 (C-A*B))
  rw [hr,hr,hr]

/-- Actual U-action normal form for EVERY bare SL3 automorphism. The inner
normalization, graph choice and common field automorphism are constructed
from Sylow/Borel geometry, actual torus kernels and A2 commutator incidence.
It asserts equality on actual U, not an unproved full-auto classification. -/
theorem actual_bare_SL3_U_action_model [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (beta : MulAut SL(3,F)) :
    ∃ (g : SL(3,F)) (a : Fin 3 → Fˣ) (phi : RingAut F) (eps : Bool),
      ∀ z ∈ upperUnipotent (F := F),
        (MulAut.conj g⁻¹*beta) z=diagonalFieldGraphAut a phi eps z := by
  classical
  obtain ⟨g,hU,hZ,hroots⟩ := actual_bare_SL3_root_normalization hF beta
  let alpha := MulAut.conj g⁻¹*beta
  rcases hroots with ⟨h0,h1⟩|⟨h0,h1⟩
  · have hr : ∀ r, (positiveRoot r).map alpha.toMonoidHom=positiveRoot (F := F) r := by
      intro r; fin_cases r
      · exact h0
      · exact h1
      · exact hZ
    obtain ⟨a,phi,hm⟩ := root_preserving_U_model alpha hr
    refine ⟨g,a,phi,false,?_⟩
    intro z hz
    simpa only [diagonalFieldGraphAut,Bool.false_eq_true,ite_false,mul_one] using hm z hz
  · let nu := alpha*tau
    have hr : ∀ r, (positiveRoot r).map nu.toMonoidHom=positiveRoot (F := F) r := by
      intro r
      change (positiveRoot r).map (alpha.toMonoidHom.comp tau.toMonoidHom)=_
      rw [← Subgroup.map_map,tau_root_image]
      fin_cases r
      · exact h1
      · exact h0
      · exact hZ
    obtain ⟨a,phi,hm⟩ := root_preserving_U_model nu hr
    refine ⟨g,a,phi,true,?_⟩
    intro z hz
    have hh := hm (tau z) ((a2Actual% tau_preserves_U) z hz)
    change alpha (tau (tau z))=diagonalFieldAut a phi (tau z) at hh
    rw [tau_involutive z] at hh
    exact hh

private theorem U_power_agreement (gamma theta : MulAut SL(3,F))
    (hstep : ∀ z ∈ upperUnipotent (F := F), gamma z=theta z)
    (hpres : ∀ z ∈ upperUnipotent (F := F), theta z ∈ upperUnipotent)
    (n : ℕ) (z : SL(3,F)) (hz : z ∈ upperUnipotent (F := F)) :
    (gamma^n) z=(theta^n) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',MulAut.mul_apply,ih,pow_succ',MulAut.mul_apply]
    exact hstep _ ((a2Actual% power_preserves_U) theta hpres n z hz)

private theorem ordered_two_actual {M : ℕ} (f : Fin (2*M) → SL(3,F)) :
    orderedProduct f=orderedProduct (fun i : Fin 2 => orderedProduct
      (fun j : Fin M => f (finProdFinEquiv (i,j)))) := (a2Actual% ordered_two) f

private theorem inner_correction (alpha : MulAut SL(3,F)) (H : SL(3,F)) :
    alpha*MulAut.conj (alpha.symm H⁻¹)⁻¹=MulAut.conj H*alpha := by
  apply MulEquiv.ext
  intro z
  simp only [MulAut.mul_apply,MulAut.conj_inv_apply,MulAut.conj_apply,map_mul,map_inv,
    MulEquiv.apply_symm_apply,inv_inv]

private theorem actual_model_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (alpha : Fin 3 → Fin M → MulAut SL(3,F))
    (a : Fin 3 → Fin M → Fin 3 → Fˣ) (phi : Fin 3 → Fin M → RingAut F)
    (eps : Fin 3 → Fin M → Bool)
    (hm : ∀ r j z, z ∈ upperUnipotent (F := F) →
      alpha r j z=diagonalFieldGraphAut (a r j) (phi r j) (eps r j) z)
    (e : Fin 3 → Fin M → ℕ) (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → SL(3,F), (∀ r j, c r j ∈ upperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((alpha r j*MulAut.conj (y r j)⁻¹)^(q/e r j)) (c r j)))) = target := by
  classical
  obtain ⟨l0,hl0,ym0,hym0,hcover0⟩ := actual_mixed_graph_root01_product hq hM hF
    (a 0) (phi 0) (eps 0) (e 0) (he 0)
  obtain ⟨l1,hl1,ym1,hym1,hcover1⟩ := actual_mixed_graph_root12_product hq hM hF
    (a 1) (phi 1) (eps 1) (e 1) (he 1)
  let model := fun r j => diagonalFieldGraphAut (a r j) (phi r j) (eps r j)
  let H0 := fun j => if eps 0 j then H (l0 j) (hl0 j)
    else diag2n (show (0:Fin 3) ≠ 1 by decide) (l0 j) (hl0 j)
  let H1 := fun j => if eps 1 j then tau (H (l1 j) (hl1 j))
    else diag2n (show (1:Fin 3) ≠ 2 by decide) (l1 j) (hl1 j)
  let y0 := fun j => (alpha 0 j).symm (H0 j)⁻¹
  let y1 := fun j => (alpha 1 j).symm (H1 j)⁻¹
  let gm0 := fun j => model 0 j*MulAut.conj (ym0 j)⁻¹
  let gm1 := fun j => model 1 j*MulAut.conj (ym1 j)⁻¹
  have hpm0 : ∀ j z, z ∈ upperUnipotent → gm0 j z ∈ upperUnipotent := by
    intro j z hz
    dsimp only [gm0,model]
    rw [hym0 j,MulAut.mul_apply]
    have hb := (a2Actual% beta_preserves_U) (a 0 j) (phi 0 j) (eps 0 j) z hz
    cases hs : eps 0 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
        (show (0:Fin 3) ≠ 1 by decide) (l0 j) (hl0 j) _ hb
    · simpa only [hs,ite_true] using (a2Actual% H_preserves_U) (l0 j) (hl0 j) _ hb
  have hpm1 : ∀ j z, z ∈ upperUnipotent → gm1 j z ∈ upperUnipotent := by
    intro j z hz
    dsimp only [gm1,model]
    rw [hym1 j,MulAut.mul_apply]
    have hb := (a2Actual% beta_preserves_U) (a 1 j) (phi 1 j) (eps 1 j) z hz
    cases hs : eps 1 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
        (show (1:Fin 3) ≠ 2 by decide) (l1 j) (hl1 j) _ hb
    · simpa only [hs,ite_true] using (a2Actual% mirrored_H_preserves_U) (l1 j) (hl1 j) _ hb
  have hagree0 : ∀ j n z, z ∈ upperUnipotent →
      ((alpha 0 j*MulAut.conj (y0 j)⁻¹)^n) z=(gm0 j^n) z := by
    intro j n z hz
    apply U_power_agreement _ _ ?_ (hpm0 j) n z hz
    intro w hw
    dsimp only [gm0,model]
    rw [inner_correction,hym0 j]
    change H0 j*alpha 0 j w*(H0 j)⁻¹=H0 j*model 0 j w*(H0 j)⁻¹
    rw [hm 0 j w hw]
  have hagree1 : ∀ j n z, z ∈ upperUnipotent →
      ((alpha 1 j*MulAut.conj (y1 j)⁻¹)^n) z=(gm1 j^n) z := by
    intro j n z hz
    apply U_power_agreement _ _ ?_ (hpm1 j) n z hz
    intro w hw
    dsimp only [gm1,model]
    rw [inner_correction,hym1 j]
    change H1 j*alpha 1 j w*(H1 j)⁻¹=H1 j*model 1 j w*(H1 j)⁻¹
    rw [hm 1 j w hw]
  let chi : Fin M → F := fun j => if eps 2 j then -((a 2 j 0:F)*(↑(a 2 j 2)⁻¹:F))
    else (a 2 j 0:F)*(↑(a 2 j 2)⁻¹:F)
  have hchi : ∀ j, chi j ≠ 0 := by
    intro j; dsimp only [chi]; split_ifs
    · exact neg_ne_zero.mpr (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    · exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have hcentral : ∀ j t, alpha 2 j (rt 2 t)=rt 2 (chi j*phi 2 j t) := by
    intro j t
    rw [hm 2 j _ ((a2Kernel% root_mem) 2 t)]
    change diagonalFieldGraphAut (a 2 j) (phi 2 j) (eps 2 j)
      (transvection (show (0:Fin 3) ≠ 2 by decide) t)=
      transvection (show (0:Fin 3) ≠ 2 by decide) (chi j*phi 2 j t)
    cases hs : eps 2 j
    · simp only [diagonalFieldGraphAut,hs,Bool.false_eq_true,ite_false,mul_one,chi]
      rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    · simp only [diagonalFieldGraphAut,hs,ite_true,MulAut.mul_apply,tau_T02,chi]
      rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root),map_neg]
      congr 1
      ring
  have hMq : q*(2*q+1) < M := lt_of_le_of_lt (by nlinarith) hM
  have hFq : 2*(2*q+1)^q < Fintype.card F := lt_of_le_of_lt
    (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (by omega) q)) hF
  have hd : ∀ j, 0 < q/e 2 j ∧ q/e 2 j ∣ q := by
    intro j
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he 2 j).2) (he 2 j).1,Nat.div_dvd_of_dvd (he 2 j).2⟩
  obtain ⟨y2,hcover2⟩ := PartIITransvectionSupply.actual_transvection_scalar_product
    (show (0:Fin 3) ≠ 2 by decide) hq hMq hFq (alpha 2) (phi 2) chi hchi
    (fun j => q/e 2 j) hd hcentral
  let g0 := fun j => (alpha 0 j*MulAut.conj (y0 j)⁻¹)^(q/e 0 j)
  let g1 := fun j => (alpha 1 j*MulAut.conj (y1 j)⁻¹)^(q/e 1 j)
  have hp0 : ∀ j z, z ∈ upperUnipotent → g0 j z ∈ upperUnipotent := by
    intro j z hz
    rw [hagree0 j _ z hz]
    exact (a2Actual% power_preserves_U) _ (hpm0 j) _ z hz
  have hp1 : ∀ j z, z ∈ upperUnipotent → g1 j z ∈ upperUnipotent := by
    intro j z hz
    rw [hagree1 j _ z hz]
    exact (a2Actual% power_preserves_U) _ (hpm1 j) _ z hz
  let G : Fin 2 → Fin M → MulAut SL(3,F) := ![g0,g1]
  let gamma : Fin (2*M) → MulAut SL(3,F) := fun k => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hgamma : ∀ k z, z ∈ upperUnipotent → gamma k z ∈ upperUnipotent := by
    intro k z hz
    dsimp only [gamma]
    rcases finProdFinEquiv.symm k with ⟨r,j⟩
    fin_cases r
    · exact hp0 j z hz
    · exact hp1 j z hz
  let y : Fin 3 → Fin M → SL(3,F) := ![y0,y1,y2]
  refine ⟨y,?_⟩
  intro target ht
  obtain ⟨A,B,C,rfl⟩ := ht
  obtain ⟨t0,ht0⟩ := hcover0 A
  obtain ⟨t1,ht1⟩ := hcover1 B
  let X : Fin 2 → Fin M → SL(3,F) := ![fun j => rt 0 (t0 j),fun j => rt 1 (t1 j)]
  let R : Fin 2 → Fin M → ℕ := ![fun j => if eps 0 j then 2 else 1,fun j => if eps 1 j then 2 else 1]
  let x := fun k : Fin (2*M) => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let r := fun k : Fin (2*M) => R (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hx : ∀ k, x k ∈ upperUnipotent := by
    intro k; dsimp only [x]
    rcases finProdFinEquiv.symm k with ⟨i,j⟩
    fin_cases i
    · exact (a2Kernel% root_mem) 0 (t0 j)
    · exact (a2Kernel% root_mem) 1 (t1 j)
  have ht0' : orderedProduct (fun j => (rt 0 (t0 j))⁻¹ *
      ((g0 j)^(if eps 0 j then 2 else 1)) (rt 0 (t0 j)))=rt 0 A := by
    simp only [g0,← pow_mul,Nat.mul_comm]
    simp_rw [hagree0 _ _ _ ((a2Kernel% root_mem) 0 _)]
    exact ht0
  have ht1' : orderedProduct (fun j => (rt 1 (t1 j))⁻¹ *
      ((g1 j)^(if eps 1 j then 2 else 1)) (rt 1 (t1 j)))=rt 1 B := by
    simp only [g1,← pow_mul,Nat.mul_comm]
    simp_rw [hagree1 _ _ _ ((a2Kernel% root_mem) 1 _)]
    exact ht1
  have hblocks : ∀ i : Fin 2, orderedProduct (fun j : Fin M =>
      (x (finProdFinEquiv (i,j)))⁻¹*(gamma (finProdFinEquiv (i,j))^r (finProdFinEquiv (i,j)))
        (x (finProdFinEquiv (i,j))))=(![rt 0 A,rt 1 B] : Fin 2 → SL(3,F)) i := by
    intro i
    simp only [x,r,gamma,Equiv.symm_apply_apply]
    fin_cases i
    · simpa [X,R,G] using ht0'
    · simpa [X,R,G] using ht1'
  have hhigh : orderedProduct (fun k => (x k)⁻¹*(gamma k^r k) (x k))=upper3 A B (A*B) := by
    rw [ordered_two_actual]
    have hh := congrArg orderedProduct (funext hblocks)
    rw [hh]
    have hmat : rt 0 A*rt 1 B*rt 2 (A*B-A*B)=upper3 A B (A*B) :=
      (a2Kernel% three_root_product) A B (A*B)
    have hz : rt (F := F) 2 0=1 := transvection_coeff_zero _
    simpa [orderedProduct,List.ofFn_succ,hz] using hmat
  obtain ⟨cp,hcp,z,hpv⟩ := PartIIA2ExponentDescent.actual_A2_power_value_descent gamma hgamma x hx r
  rw [hhigh] at hpv
  obtain ⟨t2,ht2⟩ := hcover2 (C-A*B-z)
  change orderedProduct (fun j => (rt 2 (t2 j))⁻¹*
    (((alpha 2 j*MulAut.conj (y2 j)⁻¹)^(q/e 2 j)) (rt 2 (t2 j))))=rt 2 (C-A*B-z) at ht2
  let c : Fin 3 → Fin M → SL(3,F) := ![fun j => cp (finProdFinEquiv (0,j)),
    fun j => cp (finProdFinEquiv (1,j)),fun j => rt 2 (t2 j)]
  refine ⟨c,?_,?_⟩
  · intro i j; fin_cases i
    · exact hcp _
    · exact hcp _
    · exact (a2Kernel% root_mem) 2 _
  · have hpref : orderedProduct (fun k => (cp k)⁻¹*gamma k (cp k))=
        orderedProduct (fun j => (cp (finProdFinEquiv (0,j)))⁻¹*g0 j (cp (finProdFinEquiv (0,j)))) *
          orderedProduct (fun j => (cp (finProdFinEquiv (1,j)))⁻¹*g1 j (cp (finProdFinEquiv (1,j)))) := by
      rw [ordered_two_actual]
      simp only [gamma,Equiv.symm_apply_apply]
      simp [orderedProduct,List.ofFn_succ,G]
    have hout : ∀ f : Fin 3 → SL(3,F), orderedProduct f=f 0*f 1*f 2 := by
      intro f; simp [orderedProduct,List.ofFn_succ,mul_assoc]
    rw [hout]
    change orderedProduct (fun j => (cp (finProdFinEquiv (0,j)))⁻¹*g0 j (cp (finProdFinEquiv (0,j)))) *
      orderedProduct (fun j => (cp (finProdFinEquiv (1,j)))⁻¹*g1 j (cp (finProdFinEquiv (1,j)))) *
        orderedProduct (fun j => (rt 2 (t2 j))⁻¹*
          (((alpha 2 j*MulAut.conj (y2 j)⁻¹)^(q/e 2 j)) (rt 2 (t2 j))))=upper3 A B C
    rw [← hpref,hpv,ht2]
    have hchart : rt 2 (C-A*B-z)=upper3 0 0 (C-A*B-z) := by
      change transvection (show (0:Fin 3) ≠ 2 by decide) (C-A*B-z)=upper3 0 0 (C-A*B-z)
      apply Subtype.ext; ext i j
      fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
    rw [hchart,(a2Kernel% upper3_mul),(a2Kernel% upper3_mul)]
    congr 1 <;> ring

/-- Genuine arbitrary-bare-auto A2 orbital PRODUCT. The model action,
original q/e powers, actual witnesses, ordered central correction and one
pre-target inner correction tuple are all derived/consumed. -/
theorem actual_bare_SL3_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin 3 → Fin M → MulAut SL(3,F))
    (e : Fin 3 → Fin M → ℕ) (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → SL(3,F), (∀ r j, c r j ∈ upperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((beta r j*MulAut.conj (y r j)⁻¹)^(q/e r j)) (c r j)))) = target := by
  classical
  have hsize : 4 < Fintype.card F := lt_of_le_of_lt
    (by have hh : 1 ≤ (4*q+1)^q := Nat.one_le_pow q _ (by omega); omega) hF
  choose g a phi eps hm using fun r j => actual_bare_SL3_U_action_model hsize (beta r j)
  let alpha := fun r j => MulAut.conj (g r j)⁻¹*beta r j
  obtain ⟨y,hy⟩ := actual_model_orbital_product hq hM hF alpha a phi eps hm e he
  let x := fun r j => y r j*(beta r j).symm (g r j)
  have hx : ∀ r j, beta r j*MulAut.conj (x r j)⁻¹=alpha r j*MulAut.conj (y r j)⁻¹ := by
    intro r j
    apply MulEquiv.ext; intro z
    dsimp only [alpha]
    simp only [MulAut.mul_apply,MulAut.conj_apply,inv_inv]
    dsimp only [x]
    simp only [mul_inv_rev,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  refine ⟨x,?_⟩
  intro target ht
  obtain ⟨c,hc,hprod⟩ := hy target ht
  exact ⟨c,hc,by simpa only [hx] using hprod⟩

/-- The actual three scalar blocks as ONE increasing prescribed index tuple.
This retains genuine U witnesses and corrections before all U targets. -/
theorem actual_bare_SL3_ordered_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin (3*M) → MulAut SL(3,F)) (e : Fin (3*M) → ℕ)
    (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin (3*M) → SL(3,F), (∀ j, c j ∈ upperUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹ *
          (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)))=target := by
  classical
  obtain ⟨yb,hyb⟩ := actual_bare_SL3_orbital_product hq hM hF
    (fun r j => beta (finProdFinEquiv (r,j))) (fun r j => e (finProdFinEquiv (r,j)))
    (fun r j => he _)
  let y := fun j : Fin (3*M) => yb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨y,?_⟩
  intro target ht
  obtain ⟨cb,hmem,hval⟩ := hyb target ht
  let c := fun j : Fin (3*M) => cb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨c,fun j => hmem _ _,?_⟩
  rw [(a2Kernel% ordered_blocks)]
  change orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M =>
    (c (finProdFinEquiv (r,j)))⁻¹ *
      (((beta (finProdFinEquiv (r,j))*MulAut.conj (y (finProdFinEquiv (r,j)))⁻¹)^
        (q/e (finProdFinEquiv (r,j)))) (c (finProdFinEquiv (r,j))))))=target
  simpa only [c,y,Equiv.symm_apply_apply] using hval
end NikolovSegal.PartIIA2BareOrbital
