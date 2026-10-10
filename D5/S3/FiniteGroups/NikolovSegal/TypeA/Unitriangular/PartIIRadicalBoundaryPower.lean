/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalBoundaryPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalMiddleProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Lean Elab Term in
elab "radicalPairAction%" : term => do
  let env ← getEnv
  let owner := "PartIIRadicalActions"
  let suffix := ".NikolovSegal." ++ owner ++ ".graph_pair"
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalActions"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual radical pair action not found"
open Lean Elab Term in
elab "radicalOrdered%" : term => do
  let env ← getEnv
  let owner := "PartIIRadicalMiddleProduct"
  let suffix := ".NikolovSegal." ++ owner ++ ".ordered_radical"
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalMiddleProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual ordered radical kernel not found"
namespace NikolovSegal.PartIIRadicalBoundaryPower
open PartIIRadicalCoordinates PartIIRadicalActions PartIIUnitriangularActions PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {k : ℕ}
/-- The actual exceptional pair square: coefficients of the two
opposite roots remain distinct. The diagonal determinant obstacle has
not been erased or declared an inverse transport. -/
theorem actual_pair_square (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    let R : F := (a first:F)*(((a j)⁻¹:Fˣ):F)
    let C : F := (a j.rev:F)*(((a last)⁻¹:Fˣ):F)
    let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
    (beta^2) g first j=R*phi (if eps then C else R)*(phi^2) (g first j) ∧
      (beta^2) g j.rev last=C*phi (if eps then R else C)*(phi^2) (g j.rev last) := by
  dsimp only
  let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
  let R : F := (a first:F)*(((a j)⁻¹:Fˣ):F)
  let C : F := (a j.rev:F)*(((a last)⁻¹:Fˣ):F)
  have h1 := radicalPairAction% a phi eps g hg j hj0 hjl
  have h2 := radicalPairAction% a phi eps (beta g)
    (actual_diagonal_field_graph_radical_mem a phi eps g hg) j hj0 hjl
  change beta g first j=R*(if eps then (-1:F)^(j.val+1)*phi (g j.rev last) else phi (g first j)) ∧
    beta g j.rev last=C*(if eps then (-1:F)^(j.val+1)*phi (g first j) else phi (g j.rev last)) at h1
  change beta (beta g) first j=R*(if eps then (-1:F)^(j.val+1)*phi (beta g j.rev last) else phi (beta g first j)) ∧
    beta (beta g) j.rev last=C*(if eps then (-1:F)^(j.val+1)*phi (beta g first j) else phi (beta g j.rev last)) at h2
  have hs : (-1:F)^(j.val+1)*(-1:F)^(j.val+1)=1 := by
    rw [← pow_two,← pow_mul,mul_comm (j.val+1) 2,pow_mul]; simp
  change (beta^2) g first j=R*phi (if eps then C else R)*(phi^2) (g first j) ∧
    (beta^2) g j.rev last=C*phi (if eps then R else C)*(phi^2) (g j.rev last)
  cases eps <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h1 h2 ⊢
  all_goals
    rw [pow_two,MulAut.mul_apply]
    change beta (beta g) first j=_ ∧ beta (beta g) j.rev last=_
    rw [h2.1,h2.2,h1.1,h1.2]
    change R*_=_ ∧ C*_=_
    simp only [map_mul,map_pow,map_neg,map_one,pow_two,RingAut.mul_apply]
  · constructor <;> ring
  · constructor
    · calc
        _ = R*phi C*((-1:F)^(j.val+1)*(-1:F)^(j.val+1))*phi (phi (g first j)) := by ring
        _ = _ := by rw [hs]; ring
    · calc
        _ = C*phi R*((-1:F)^(j.val+1)*(-1:F)^(j.val+1))*phi (phi (g j.rev last)) := by ring
        _ = _ := by rw [hs]; ring
private def rowCoefficient (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (j : Fin (k+2)) : F :=
  let R := (a first:F)*(((a j)⁻¹:Fˣ):F)
  let C := (a j.rev:F)*(((a last)⁻¹:Fˣ):F)
  R*phi (if eps then C else R)
private def columnCoefficient (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (j : Fin (k+2)) : F :=
  let R := (a first:F)*(((a j)⁻¹:Fˣ):F)
  let C := (a j.rev:F)*(((a last)⁻¹:Fˣ):F)
  C*phi (if eps then R else C)
/-- Every actual even power, with distinct nonzero exceptional scalars;
this is the concrete coefficient normalization needed before Lemma7.1. -/
theorem actual_even_pair_power (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) (d : ℕ) :
    let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
    InRadical ((beta^(2*d)) g) ∧
      (beta^(2*d)) g first j=orbitProduct (phi^2) d (rowCoefficient a phi eps j)*((phi^2)^d) (g first j) ∧
      (beta^(2*d)) g j.rev last=orbitProduct (phi^2) d (columnCoefficient a phi eps j)*((phi^2)^d) (g j.rev last) := by
  dsimp only
  let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
  induction d with
  | zero => simpa [orbitProduct] using hg
  | succ d ih =>
    have hs := actual_pair_square a phi eps ((beta^(2*d)) g) ih.1 j hj0 hjl
    have hb := actual_diagonal_field_graph_radical_mem a phi eps ((beta^(2*d)) g) ih.1
    have hbb := actual_diagonal_field_graph_radical_mem a phi eps (beta ((beta^(2*d)) g)) hb
    rw [show 2*(d+1)=2+2*d by omega,pow_add,MulAut.mul_apply]
    refine ⟨?_,?_⟩
    · simpa only [pow_two,MulAut.mul_apply] using hbb
    · change (beta^2) ((beta^(2*d)) g) first j=_ ∧ (beta^2) ((beta^(2*d)) g) j.rev last=_
      change (beta^2) ((beta^(2*d)) g) first j=rowCoefficient a phi eps j*(phi^2) (((beta^(2*d)) g) first j) ∧
        (beta^2) ((beta^(2*d)) g) j.rev last=columnCoefficient a phi eps j*(phi^2) (((beta^(2*d)) g) j.rev last) at hs
      rw [hs.1,hs.2,ih.2.1,ih.2.2]
      rw [(rootFieldKernel% orbitProduct_succ),(rootFieldKernel% orbitProduct_succ)]
      simp only [map_mul,pow_succ',RingAut.mul_apply]
      constructor <;> ring
/-- Actual original-d-power boundary VALUE, with its genuinely distinct
scalar coefficients. These depend on the prescribed action BEFORE any
target; the commutator witness itself carries the target parameters. -/
theorem actual_boundary_norm_value (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) (d : ℕ) :
    let beta := (PartIIProposition6_5.diagonalFieldGraph a phi eps)^d
    let x := g*beta g
    InRadical x ∧ InRadical (x⁻¹*beta x) ∧
      (x⁻¹*beta x) first j=orbitProduct (phi^2) d (rowCoefficient a phi eps j)*((phi^2)^d) (g first j)-g first j ∧
      (x⁻¹*beta x) j.rev last=orbitProduct (phi^2) d (columnCoefficient a phi eps j)*((phi^2)^d) (g j.rev last)-g j.rev last := by
  dsimp only
  let gamma := PartIIProposition6_5.diagonalFieldGraph a phi eps
  let beta := gamma^d
  let x := g*beta g
  have hpres : ∀ e (w : Matrix.SpecialLinearGroup (Fin (k+2)) F), InRadical w → InRadical ((gamma^e) w) := by
    intro e
    induction e with
    | zero => intro w hw; simpa only [pow_zero,MulAut.one_apply] using hw
    | succ e ih =>
      intro w hw
      rw [pow_succ',MulAut.mul_apply]
      exact actual_diagonal_field_graph_radical_mem a phi eps _ (ih w hw)
  have hb : InRadical (beta g) := hpres d g hg
  have hx : InRadical x := actual_radical_product_mem g (beta g) hg hb
  have hbx : InRadical (beta x) := hpres d x hx
  have hbb : InRadical (beta (beta g)) := hpres d (beta g) hb
  have hjr0 : j.rev≠first := by
    intro h; have he := congrArg Fin.rev h; apply hjl; simpa [first,last] using he
  have hjrl : j.rev≠last := by
    intro h; have he := congrArg Fin.rev h; apply hj0; simpa [first,last] using he
  have hv := actual_radical_product_row_column x⁻¹ (beta x) (actual_radical_inverse_mem x hx) hbx j hj0 hjl
  have hvr := actual_radical_product_row_column x⁻¹ (beta x) (actual_radical_inverse_mem x hx) hbx j.rev hjr0 hjrl
  have hxi := actual_radical_inverse_row_column x hx j hj0 hjl
  have hxir := actual_radical_inverse_row_column x hx j.rev hjr0 hjrl
  have hxx := actual_radical_product_row_column g (beta g) hg hb j hj0 hjl
  have hxxr := actual_radical_product_row_column g (beta g) hg hb j.rev hjr0 hjrl
  have hbxx := actual_radical_product_row_column (beta g) (beta (beta g)) hb hbb j hj0 hjl
  have hbxxr := actual_radical_product_row_column (beta g) (beta (beta g)) hb hbb j.rev hjr0 hjrl
  have he : beta (beta g)=(gamma^(2*d)) g := by
    simp only [beta,← MulAut.mul_apply,← pow_add,show d+d=2*d by omega]
  have hp := actual_even_pair_power a phi eps g hg j hj0 hjl d
  refine ⟨hx,actual_radical_product_mem _ _ (actual_radical_inverse_mem x hx) hbx,?_⟩
  constructor
  · rw [hv.1,hxi.1]
    change -(g*beta g) first j+beta (g*beta g) first j=_
    rw [map_mul,hxx.1,hbxx.1,he,hp.2.1]; ring
  · rw [hvr.2,hxir.2]
    change -(g*beta g) j.rev last+beta (g*beta g) j.rev last=_
    rw [map_mul,hxxr.2,hbxxr.2,he,hp.2.2]; ring
private def boundaryTorus (lambda : Fˣ) : Fin (k+2) → Fˣ :=
  Fin.cons lambda (Fin.snoc (fun _ : Fin k => 1) lambda⁻¹)
private theorem boundaryTorus_product (lambda : Fˣ) : ∏ i : Fin (k+2), boundaryTorus lambda i=1 := by
  simp [boundaryTorus,Fin.prod_cons,Fin.prod_snoc]
private theorem boundaryTorus_first_last (lambda : Fˣ) :
    boundaryTorus lambda (first : Fin (k+2))=lambda ∧
      boundaryTorus lambda (last : Fin (k+2))=lambda⁻¹ := by
  constructor
  · simp [boundaryTorus,first]
  · have he : (last : Fin (k+2))=(Fin.last k).succ := by apply Fin.ext; rfl
    rw [he]; simp [boundaryTorus]
private theorem boundaryTorus_interior (lambda : Fˣ) (j : Fin (k+2))
    (hj0 : j≠first) (hjl : j≠last) : boundaryTorus lambda j=1 := by
  refine Fin.cases (fun h0 hl => False.elim (h0 rfl)) (fun i hi0 hil => ?_) j hj0 hjl
  refine Fin.lastCases (fun h => False.elim (h rfl)) (fun i h => ?_) i hil
  simp [boundaryTorus]
private theorem torus_coefficients (a : Fin (k+2) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    rowCoefficient (fun i => boundaryTorus lambda i*a i) phi eps j=
      (lambda:F)*phi (lambda:F)*rowCoefficient a phi eps j ∧
    columnCoefficient (fun i => boundaryTorus lambda i*a i) phi eps j=
      (lambda:F)*phi (lambda:F)*columnCoefficient a phi eps j := by
  have hr0 : j.rev≠first := by
    intro h; have he := congrArg Fin.rev h; apply hjl; simpa [first,last] using he
  have hrl : j.rev≠last := by
    intro h; have he := congrArg Fin.rev h; apply hj0; simpa [first,last] using he
  have he := boundaryTorus_first_last (k:=k) lambda
  cases eps <;> simp only [rowCoefficient,columnCoefficient,ite_false,ite_true,Bool.false_eq_true,
    he.1,he.2,boundaryTorus_interior lambda j hj0 hjl,boundaryTorus_interior lambda j.rev hr0 hrl,
    one_mul,Units.val_mul,_root_.mul_inv_rev,inv_inv,Units.val_inv_eq_inv_val,map_mul]
  all_goals constructor <;> ring
private theorem paired_orbit_product (phi : RingAut F) (lambda : F) (d : ℕ) :
    orbitProduct (phi^2) d (lambda*phi lambda)=orbitProduct phi (2*d) lambda := by
  induction d with
  | zero => simp [orbitProduct]
  | succ d ih =>
    rw [(rootFieldKernel% orbitProduct_succ),ih]
    have hN : orbitProduct phi (2*(d+1)) lambda=
        lambda*phi lambda*phi (phi (orbitProduct phi (2*d) lambda)) := by
      rw [show 2*(d+1)=(2*d+1)+1 by omega,(rootFieldKernel% orbitProduct_succ),
        (rootFieldKernel% orbitProduct_succ),map_mul]; ring
    rw [hN]
    simp only [pow_two,RingAut.mul_apply]
private theorem orbit_product_mul (phi : RingAut F) (a b : F) (d : ℕ) :
    orbitProduct phi d (a*b)=orbitProduct phi d a*orbitProduct phi d b := by
  simp [orbitProduct,map_mul,Finset.prod_mul_distrib]
/-- Exact lambda normalization for the actual exceptional scalar tuple.
The residual mu is fixed by a/phi/eps/d, BEFORE every target. -/
theorem actual_boundary_torus_orbit_factors (a : Fin (k+2) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) (d : ℕ) :
    orbitProduct (phi^2) d (rowCoefficient (fun i => boundaryTorus lambda i*a i) phi eps j)=
      orbitProduct phi (2*d) (lambda:F)*orbitProduct (phi^2) d (rowCoefficient a phi eps j) ∧
    orbitProduct (phi^2) d (columnCoefficient (fun i => boundaryTorus lambda i*a i) phi eps j)=
      orbitProduct phi (2*d) (lambda:F)*orbitProduct (phi^2) d (columnCoefficient a phi eps j) := by
  have he := torus_coefficients a lambda phi eps j hj0 hjl
  rw [he.1,he.2]
  constructor
  · rw [orbit_product_mul,paired_orbit_product]
  · rw [orbit_product_mul,paired_orbit_product]
/-- The pre-target scalar tuple really is nonzero: it is a product of
actual diagonal-unit weights and their genuine field images. -/
theorem actual_boundary_scalar_nonzero (a : Fin (k+2) → Fˣ) (phi : RingAut F)
    (eps : Bool) (j : Fin (k+2)) (d : ℕ) :
    orbitProduct (phi^2) d (rowCoefficient a phi eps j)≠0 ∧
      orbitProduct (phi^2) d (columnCoefficient a phi eps j)≠0 := by
  have hphi : ∀ x : F, x≠0 → phi x≠0 := by
    intro x hx he; apply hx; apply phi.injective; simpa using he
  have hR : (a first:F)*(((a j)⁻¹:Fˣ):F)≠0 := mul_ne_zero (a first).ne_zero ((a j)⁻¹).ne_zero
  have hC : (a j.rev:F)*(((a last)⁻¹:Fˣ):F)≠0 := mul_ne_zero (a j.rev).ne_zero ((a last)⁻¹).ne_zero
  have hcoeff : rowCoefficient a phi eps j≠0 ∧ columnCoefficient a phi eps j≠0 := by
    cases eps <;> simp only [rowCoefficient,columnCoefficient,ite_true,ite_false,Bool.false_eq_true]
    · exact ⟨mul_ne_zero hR (hphi _ hR),mul_ne_zero hC (hphi _ hC)⟩
    · exact ⟨mul_ne_zero hR (hphi _ hC),mul_ne_zero hC (hphi _ hR)⟩
  constructor
  · unfold orbitProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi he; apply hcoeff.1; apply ((phi^2)^i).injective; exact he.trans (map_zero ((phi^2)^i)).symm
  · unfold orbitProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi he; apply hcoeff.2; apply ((phi^2)^i).injective; exact he.trans (map_zero ((phi^2)^i)).symm
/-- Concrete determinant-one torus correction, before target witnesses. -/
theorem actual_boundary_inner_torus (a : Fin (k+2) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) :
    ∃ h : Matrix.SpecialLinearGroup (Fin (k+2)) F,
      (∀ i j, i≠j → h i j=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph a phi eps=
        PartIIProposition6_5.diagonalFieldGraph (fun i => boundaryTorus lambda i*a i) phi eps := by
  apply PartIIRadicalInnerTorus.actual_diagonal_inner_normalization
  simp only [Finset.prod_mul_distrib,boundaryTorus_product,one_mul]
/-- Actual normalized fieldValue, consuming the original-power norm
witness and the exact lambda orbit factor. This closes coefficient
normalization; full boundary support/PRODUCT assembly remains separate. -/
theorem actual_boundary_norm_field_value (a : Fin (k+2) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (hg : InRadical g) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) (d : ℕ) :
    let beta := (PartIIProposition6_5.diagonalFieldGraph (fun i => boundaryTorus lambda i*a i) phi eps)^d
    let x := g*beta g
    InRadical x ∧ InRadical (x⁻¹*beta x) ∧
      (x⁻¹*beta x) first j=fieldValue phi (orbitProduct (phi^2) d (rowCoefficient a phi eps j)) (2*d) 1 (lambda:F) (g first j) ∧
      (x⁻¹*beta x) j.rev last=fieldValue phi (orbitProduct (phi^2) d (columnCoefficient a phi eps j)) (2*d) 1 (lambda:F) (g j.rev last) := by
  dsimp only
  have hv := actual_boundary_norm_value (fun i => boundaryTorus lambda i*a i) phi eps g hg j hj0 hjl d
  have he := actual_boundary_torus_orbit_factors a lambda phi eps j hj0 hjl d
  refine ⟨hv.1,hv.2.1,?_⟩
  constructor
  · rw [hv.2.2.1,he.1]
    simp only [fieldValue,pow_one,← pow_mul]; ring
  · rw [hv.2.2.2,he.2]
    simp only [fieldValue,pow_one,← pow_mul]; ring
/-- Genuine bounded-length boundary-axis PRODUCT in V modulo its
corner: every off-axis coordinate is proved zero. The same actual
INNER tuple precedes ALL scalar targets. No coverage premise remains. -/
theorem actual_inner_radical_axis_product [Fintype F] [DecidableEq F]
    {l q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q)<Fintype.card F)
    (a : Fin M → Fin (l+3) → Fˣ) (phi : Fin M → RingAut F)
    (eps : Fin M → Bool) (d : Fin M → ℕ) (hd : ∀ i, 0<d i ∧ d i ∣ q)
    (j : Fin (l+3)) (hj0 : j≠first) (hjl : j≠last) (side : Bool) :
    ∃ h : Fin M → Matrix.SpecialLinearGroup (Fin (l+3)) F,
      (∀ i r c, r≠c → h i r c=0) ∧ ∀ target : F,
      ∃ x : Fin M → Matrix.SpecialLinearGroup (Fin (l+3)) F,
        (∀ i, InRadical (x i)) ∧
        let P := NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
          ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))
        InRadical P ∧ ∀ j' : Fin (l+3), j'≠first → j'≠last →
          P first j'=(if j'=j then (if side then 0 else target) else 0) ∧
          P j'.rev last=(if j'=j then (if side then target else 0) else 0) := by
  classical
  let mu : Fin M → F := fun i => if side then
    orbitProduct (phi i^2) (d i) (columnCoefficient (a i) (phi i) (eps i) j) else
    orbitProduct (phi i^2) (d i) (rowCoefficient (a i) (phi i) (eps i) j)
  have hmu : ∀ i, mu i≠0 := by
    intro i
    have he := actual_boundary_scalar_nonzero (a i) (phi i) (eps i) j (d i)
    cases side
    · exact he.1
    · exact he.2
  have hd2 : ∀ i, 0<2*d i ∧ 2*d i ∣ 2*q := fun i =>
    ⟨by have hh := (hd i).1; omega,Nat.mul_dvd_mul_left 2 (hd i).2⟩
  obtain ⟨lam,hlam,hs⟩ := lemma7_1 (c:=1) (q:=2*q) (by omega)
    (by simpa using hM) (by simpa using hF) phi mu (fun i => 2*d i) (fun _ => 1)
    hmu hd2 (fun _ => by simp)
  let lambda : Fin M → Fˣ := fun i => Units.mk0 (lam i) (hlam i)
  have hh : ∀ i, ∃ h : Matrix.SpecialLinearGroup (Fin (l+3)) F,
      (∀ r c, r≠c → h r c=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)=
        PartIIProposition6_5.diagonalFieldGraph (fun r => boundaryTorus (lambda i) r*a i r) (phi i) (eps i) := by
    intro i; exact actual_boundary_inner_torus (a i) (lambda i) (phi i) (eps i)
  choose h hh he using hh
  refine ⟨h,hh,?_⟩
  intro target
  obtain ⟨t,ht⟩ := hs target
  have hjr0 : j.rev≠first := by
    intro h; have he := congrArg Fin.rev h; apply hjl; simpa [first,last] using he
  have hjrl : j.rev≠last := by
    intro h; have he := congrArg Fin.rev h; apply hj0; simpa [first,last] using he
  let r : Fin M → Fin (l+3) → F := fun i s => if side then 0 else if s=j then t i else 0
  let c : Fin M → Fin (l+3) → F := fun i s => if side then (if s=j.rev then t i else 0) else 0
  have hr : ∀ i, EndpointZero (r i) := by
    intro i; constructor <;> simp [r,Ne.symm hj0,Ne.symm hjl]
  have hc : ∀ i, EndpointZero (c i) := by
    intro i; constructor <;> simp [c,Ne.symm hjr0,Ne.symm hjrl]
  let g := fun i => radical (r i) (c i) (hr i) (hc i) 0
  have hg : ∀ i, InRadical (g i) := fun i => actual_radical_mem _ _ _ _ _
  let beta := fun i => (PartIIProposition6_5.diagonalFieldGraph
    (fun s => boundaryTorus (lambda i) s*a i s) (phi i) (eps i))^(d i)
  let x := fun i => g i*beta i (g i)
  let v := fun i => (x i)⁻¹*beta i (x i)
  have hv := fun i => actual_boundary_norm_field_value (a i) (lambda i) (phi i) (eps i) (g i) (hg i) j hj0 hjl (d i)
  have hP := radicalOrdered% v (fun i => (hv i).2.1)
  refine ⟨x,fun i => (hv i).1,?_⟩
  simp only [he]
  change InRadical (NikolovSegal.orderedProduct v) ∧ _
  refine ⟨hP.1,?_⟩
  intro j' hj'0 hj'l
  have hj'r0 : j'.rev≠first := by
    intro h; have he := congrArg Fin.rev h; apply hj'l; simpa [first,last] using he
  have hj'rl : j'.rev≠last := by
    intro h; have he := congrArg Fin.rev h; apply hj'0; simpa [first,last] using he
  rw [(hP.2 j' hj'0 hj'l).1,(hP.2 j'.rev hj'r0 hj'rl).2]
  have hval := fun i => actual_boundary_norm_field_value (a i) (lambda i) (phi i) (eps i)
    (g i) (hg i) j' hj'0 hj'l (d i)
  have hR : ∀ i, g i first j'=r i j' := fun i => actual_radical_row _ _ _ _ _ j' hj'0 hj'l
  have hC : ∀ i, g i j'.rev last=c i j'.rev := fun i => actual_radical_column _ _ _ _ _ j'.rev hj'r0 hj'rl
  by_cases hj' : j'=j
  · subst j'
    have hvalsR : ∀ i, v i first j=fieldValue (phi i)
        (orbitProduct (phi i^2) (d i) (rowCoefficient (a i) (phi i) (eps i) j)) (2*d i) 1 (lam i) (if side then 0 else t i) := by
      intro i; rw [(hval i).2.2.1,hR i]; simp only [r,ite_true]; rfl
    have hvalsC : ∀ i, v i j.rev last=fieldValue (phi i)
        (orbitProduct (phi i^2) (d i) (columnCoefficient (a i) (phi i) (eps i) j)) (2*d i) 1 (lam i) (if side then t i else 0) := by
      intro i; rw [(hval i).2.2.2,hC i]; simp only [c,ite_true]; rfl
    simp only [hvalsR,hvalsC,ite_true]
    cases side
    · constructor
      · exact ht
      · simp [fieldValue]
    · constructor
      · simp [fieldValue]
      · exact ht
  · have hrev : j'.rev≠j.rev := by
      intro h; apply hj'; have he := congrArg Fin.rev h; simpa only [Fin.rev_rev] using he
    have hvalsR : ∀ i, v i first j'=0 := by
      intro i; rw [(hval i).2.2.1,hR i]
      simp [r,hj',fieldValue]
    have hvalsC : ∀ i, v i j'.rev last=0 := by
      intro i; rw [(hval i).2.2.2,hC i]
      simp [c,hrev,fieldValue]
    simp [hj',hvalsR,hvalsC]
end NikolovSegal.PartIIRadicalBoundaryPower
