/- GID: D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Numbered-path offset composition and the three-associator triangle modulo three. -/

import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates

/- The small internal carrier records only the equivariance that the actual
   numbered-edge maps below possess. It introduces no orbit/basis substitute. -/
private structure PathCoding {n m : ℕ} (A : CountMat n n) (B : CountMat m m) where
  equiv : Path A ≃ Path B
  step : Function.Semiconj equiv (shift A) (shift B)

private def PathCoding.identity {n : ℕ} (A : CountMat n n) : PathCoding A A :=
  ⟨Equiv.refl _, fun _ => rfl⟩

private def PathCoding.trans {n m p : ℕ} {A : CountMat n n} {B : CountMat m m}
    {C : CountMat p p} (f : PathCoding A B) (g : PathCoding B C) : PathCoding A C :=
  ⟨f.equiv.trans g.equiv, fun x => by
    change g.equiv (f.equiv (shift A x)) = shift C (g.equiv (f.equiv x))
    rw [f.step, g.step]⟩

private theorem pathCoding_ext {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    {f g : PathCoding A B} (h : ∀ x, f.equiv x = g.equiv x) : f = g := by
  have he : f.equiv = g.equiv := Equiv.ext h
  cases f
  cases g
  cases he
  rfl

private theorem PathCoding.period {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (f : PathCoding A B) (x : Path A) (d : ℕ) :
    Function.IsPeriodicPt (shift B) d (f.equiv x) ↔
      Function.IsPeriodicPt (shift A) d x := by
  change (shift B)^[d] (f.equiv x) = f.equiv x ↔ (shift A)^[d] x = x
  rw [← f.step.iterate_right d x]
  exact f.equiv.injective.eq_iff

private theorem PathCoding.minimalPeriod {n m : ℕ} {A : CountMat n n}
    {B : CountMat m m} (f : PathCoding A B) (x : Path A) :
    Function.minimalPeriod (shift B) (f.equiv x) =
      Function.minimalPeriod (shift A) x := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  exact f.period x

private def PathCoding.primitive {n m d : ℕ} {A : CountMat n n} {B : CountMat m m}
    (f : PathCoding A B) : PrimitivePath A d ≃ PrimitivePath B d where
  toFun x := ⟨f.equiv x.val, by rw [f.minimalPeriod, x.property]⟩
  invFun y := ⟨f.equiv.symm y.val, by
    have h := f.minimalPeriod (f.equiv.symm y.val)
    rw [Equiv.apply_symm_apply, y.property] at h
    exact h.symm⟩
  left_inv x := Subtype.ext (f.equiv.symm_apply_apply x.val)
  right_inv y := Subtype.ext (f.equiv.apply_symm_apply y.val)

private theorem PathCoding.orbit_iff {n m d : ℕ} {A : CountMat n n} {B : CountMat m m}
    (f : PathCoding A B) (x y : PrimitivePath A d) :
    SamePathOrbit (f.primitive x) (f.primitive y) ↔ SamePathOrbit x y := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q,f.equiv.injective ?_⟩
    rw [f.step.iterate_right q x.val]
    exact hq
  · rintro ⟨q,hq⟩
    refine ⟨q,?_⟩
    change (shift B)^[q] (f.equiv x.val) = f.equiv y.val
    rw [← f.step.iterate_right q x.val,hq]

private def PathCoding.orbits {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) :
    ActualPathOrbit A d ≃ ActualPathOrbit B d where
  toFun := Quotient.map f.primitive (fun x y h => (f.orbit_iff x y).mpr h)
  invFun := Quotient.map f.primitive.symm (by
    intro x y h
    change SamePathOrbit x y at h
    change SamePathOrbit (f.primitive.symm x) (f.primitive.symm y)
    apply (f.orbit_iff _ _).mp
    simpa only [Equiv.apply_symm_apply] using h)
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ (f.primitive.symm (f.primitive x)) = Quotient.mk _ x
    rw [Equiv.symm_apply_apply]
  right_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ (f.primitive (f.primitive.symm x)) = Quotient.mk _ x
    rw [Equiv.apply_symm_apply]

private def PathCoding.bases {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) :
    PathBasis A d ≃ PathBasis B d :=
  (orbitBasisEquiv A).symm.trans (f.orbits.trans (orbitBasisEquiv B))

private theorem PathCoding.bases_then {n m p d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} {C : CountMat p p}
    (f : PathCoding A B) (g : PathCoding B C) (b : PathBasis A d) :
    (f.trans g).bases b = g.bases (f.bases b) := by
  change canonicalPath ((f.trans g).primitive b.val) =
    canonicalPath (g.primitive (canonicalPath (f.primitive b.val)).val)
  apply canonicalPath_eq_of_sameOrbit
  exact (g.orbit_iff _ _).mpr (canonicalPath_sameOrbit (f.primitive b.val))

private def signedForward {n d : ℕ} [NeZero d] {A : CountMat n n}
    (x : PrimitivePath A d) : ℤ :=
  -((leastIndex (primitiveRestriction x).val (primitiveRestriction_primitive x)).val : ℤ)

private theorem residue_timeIndex {d : ℕ} [NeZero d] (q : ℤ) :
    ZMod.finEquiv d (timeIndex (d := d) q) = (q : ZMod d) := by
  rw [finEquiv_eq_natCast]
  have hv : ((timeIndex (d := d) q).val : ℤ) = q % (d : ℤ) := by
    change (((q % (d : ℤ)).toNat : ℕ) : ℤ) = q % (d : ℤ)
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d))
  calc
    ((timeIndex (d := d) q).val : ZMod d) =
        (((timeIndex (d := d) q).val : ℤ) : ZMod d) := by simp
    _ = ((q % (d : ℤ) : ℤ) : ZMod d) := congrArg (fun z : ℤ => (z : ZMod d)) hv
    _ = (q : ZMod d) := ZMod.intCast_mod q d

/- This is the actual offset equation with the literal signed forward time
   -k, before taking its residue. No positive k is substituted for it. -/
private theorem PathCoding.signed_equation {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) (b : PathBasis A d) :
    f.equiv b.val.val = translate (countedGraph B)
      (signedForward (f.primitive b.val)) (f.bases b).val.val := by
  let x : PrimitivePath B d := f.primitive b.val
  let k := leastIndex (primitiveRestriction x).val (primitiveRestriction_primitive x)
  change x.val = translate (countedGraph B) (-(k.val : ℤ)) (canonicalPath x).val.val
  rw [canonicalPath_eq_shift x]
  rw [show (shift B)^[k.val] x.val =
      translate (countedGraph B) (k.val : ℤ) x.val from
    shift_iterate_translate (countedGraph B) k.val x.val]
  apply Subtype.ext
  funext t
  change x.val.val t = x.val.val ((t + -(k.val : ℤ)) + (k.val : ℤ))
  simp only [add_assoc, neg_add_cancel, add_zero]

theorem periodic_translate_residue {n d : ℕ} [NeZero d]
    {A : CountMat n n} (x : Path A)
    (hx : Function.IsPeriodicPt (shift A) d x) (q : ℤ) :
    translate (countedGraph A) q x = (shift A)^[(timeIndex (d := d) q).val] x := by
  rw [show (shift A)^[(timeIndex (d := d) q).val] x =
      translate (countedGraph A) ((timeIndex (d := d) q).val : ℤ) x from
    shift_iterate_translate (countedGraph A) _ x]
  apply Subtype.ext
  funext t
  have hq : ((timeIndex (d := d) q).val : ℤ) = q % (d : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d))
  change x.val (t+q) = x.val (t+((timeIndex (d := d) q).val : ℤ))
  rw [hq]
  have he : (t+q % (d : ℤ))+(q/(d : ℤ))*(d : ℤ) = t+q := by
    have hm := Int.emod_add_ediv_mul q (d : ℤ)
    omega
  have h := path_period_coordinate_int_mul x hx (q/(d : ℤ)) (t+q % (d : ℤ))
  rw [he] at h
  exact h

/- The repository's translate_commutation has one shared vertex type. Here
   the dimensions may differ. On the actual primitive paths we instead consume
   the saved signed-to-natural residue reduction on EACH graph, then use step.
   This retains the literal signed q before, and after, the computation. -/
private theorem PathCoding.translate_primitive {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B)
    (x : PrimitivePath A d) (q : ℤ) :
    f.equiv (translate (countedGraph A) q x.val) =
      translate (countedGraph B) q (f.equiv x.val) := by
  rw [periodic_translate_residue x.val (primitivePath_period x) q,
    periodic_translate_residue (f.equiv x.val) (primitivePath_period (f.primitive x)) q]
  exact f.step.iterate_right _ x.val

private theorem PathCoding.offset_then {n m p d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} {C : CountMat p p}
    (f : PathCoding A B) (g : PathCoding B C) (b : PathBasis A d) :
    ZMod.finEquiv d (canonicalForwardOffset ((f.trans g).primitive b.val)) =
      ZMod.finEquiv d (canonicalForwardOffset (f.primitive b.val)) +
      ZMod.finEquiv d (canonicalForwardOffset (g.primitive (f.bases b).val)) := by
  let q := signedForward (f.primitive b.val)
  let r := signedForward (g.primitive (f.bases b).val)
  have he : (f.trans g).equiv b.val.val =
      translate (countedGraph C) (q+r) ((f.trans g).bases b).val.val := by
    change g.equiv (f.equiv b.val.val) = _
    rw [f.signed_equation]
    rw [g.translate_primitive (f.bases b).val q]
    rw [g.signed_equation, f.bases_then g b]
    apply Subtype.ext
    funext t
    change (g.bases (f.bases b)).val.val.val ((t+q)+r) =
      (g.bases (f.bases b)).val.val.val (t+(q+r))
    rw [add_assoc]
  rw [periodic_translate_residue _
    (primitivePath_period ((f.trans g).bases b).val) (q+r)] at he
  have hu : timeIndex (d := d) (q+r) =
      canonicalForwardOffset ((f.trans g).primitive b.val) := by
    apply Fin.ext
    have hp := ((f.trans g).bases b).val.property
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := shift C) (x := ((f.trans g).bases b).val.val)
      (m := (timeIndex (d := d) (q+r)).val)
      (n := (canonicalForwardOffset ((f.trans g).primitive b.val)).val)
      (by simpa only [hp] using (timeIndex (d := d) (q+r)).isLt)
      (by simpa only [hp] using
        (canonicalForwardOffset ((f.trans g).primitive b.val)).isLt)).mp
    exact he.symm.trans (canonicalForwardOffset_equation ((f.trans g).primitive b.val))
  rw [← hu, residue_timeIndex]
  rw [canonicalForwardOffset_residue,canonicalForwardOffset_residue]
  simp only [q, r, signedForward, Int.cast_add, Int.cast_neg, Int.cast_natCast]

/-- Internal orbit-offset sum on the saved actual minimal-period PATH quotient. -/
private def pathGyration {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) : ZMod d :=
  ∑ o : ActualPathOrbit A d,
    ZMod.finEquiv d (canonicalForwardOffset (f.primitive ((orbitBasisEquiv A) o).val))

private theorem pathGyration_basis {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) :
    pathGyration (d := d) f =
      ∑ b : PathBasis A d, ZMod.finEquiv d (canonicalForwardOffset (f.primitive b.val)) := by
  classical
  exact (orbitBasisEquiv (d := d) A).sum_comp
    (fun b : PathBasis A d => (ZMod.finEquiv d
      (canonicalForwardOffset (f.primitive b.val)) : ZMod d))

private theorem pathGyration_then {n m p d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} {C : CountMat p p}
    (f : PathCoding A B) (g : PathCoding B C) :
    pathGyration (d := d) (f.trans g) = pathGyration f + pathGyration g := by
  classical
  rw [pathGyration_basis,pathGyration_basis,pathGyration_basis]
  simp_rw [PathCoding.offset_then]
  rw [Finset.sum_add_distrib]
  congr 1
  exact (f.bases (d := d)).sum_comp
    (fun b : PathBasis B d => (ZMod.finEquiv d
      (canonicalForwardOffset (g.primitive b.val)) : ZMod d))

private theorem pathGyration_identity {n d : ℕ} [NeZero d] (A : CountMat n n) :
    pathGyration (d := d) (PathCoding.identity A) = 0 := by
  classical
  rw [pathGyration_basis]
  apply Finset.sum_eq_zero
  intro b _
  have h : canonicalForwardOffset b.val = 0 := by
    have he := canonicalForwardOffset_equation b.val
    rw [canonicalPath_of_basis] at he
    have hi := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := shift A) (x := b.val.val)
      (m := (canonicalForwardOffset b.val).val) (n := 0)
      (by simpa only [b.val.property] using (canonicalForwardOffset b.val).isLt)
      (by simpa only [b.val.property] using
        Nat.pos_of_ne_zero (NeZero.ne d))).mp he.symm
    exact Fin.ext (by simpa using hi)
  change ZMod.finEquiv d (canonicalForwardOffset b.val) = 0
  rw [h]
  exact map_zero _

private def elementaryCoding {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    PathCoding (R*S) (S*R) := ⟨(elementaryHomeomorph R S).toEquiv, elementary_shift R S⟩

private def pathGyrationThree {n m d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} {B : CountMat m m} (f : PathCoding A B) : ZMod 3 :=
  ZMod.castHom hd (ZMod 3) (pathGyration (d := d) f)

private theorem pathGyrationThree_then {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} {B : CountMat m m} {C : CountMat p p}
    (f : PathCoding A B) (g : PathCoding B C) :
    pathGyrationThree hd (f.trans g) = pathGyrationThree hd f + pathGyrationThree hd g := by
  simp only [pathGyrationThree,pathGyration_then,map_add]

private theorem pathGyrationThree_identity {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (A : CountMat n n) : pathGyrationThree hd (PathCoding.identity A) = 0 := by
  simp only [pathGyrationThree,pathGyration_identity,map_zero]

private theorem pathGyrationThree_involution {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (f : PathCoding A A) (hinv : ∀ x, f.equiv (f.equiv x) = x) :
    pathGyrationThree hd f = 0 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hf : f.trans f = PathCoding.identity A := pathCoding_ext hinv
  have ht := pathGyrationThree_then hd f f
  rw [hf,pathGyrationThree_identity] at ht
  have htwo : (2 : ZMod 3) * pathGyrationThree hd f = 0 := by
    simpa only [two_mul] using ht.symm
  exact (mul_eq_zero.mp htwo).resolve_left (by decide)

/- Endpoint-preserving maps and their actual coordinatewise path consumers. -/
private structure EdgeCoding {n : ℕ} (A B : CountMat n n) where
  equiv : Edge A ≃ Edge B
  source : ∀ a, (equiv a).source = a.source
  target : ∀ a, (equiv a).target = a.target

private def EdgeCoding.inverse {n : ℕ} {A B : CountMat n n} (e : EdgeCoding A B) :
    EdgeCoding B A where
  equiv := e.equiv.symm
  source b := by simpa only [Equiv.apply_symm_apply] using (e.source (e.equiv.symm b)).symm
  target b := by simpa only [Equiv.apply_symm_apply] using (e.target (e.equiv.symm b)).symm

private def EdgeCoding.trans {n : ℕ} {A B C : CountMat n n}
    (e : EdgeCoding A B) (f : EdgeCoding B C) : EdgeCoding A C where
  equiv := e.equiv.trans f.equiv
  source a := (f.source _).trans (e.source a)
  target a := (f.target _).trans (e.target a)

private def EdgeCoding.path {n : ℕ} {A B : CountMat n n} (e : EdgeCoding A B) :
    PathCoding A B where
  equiv :=
    { toFun x := ⟨fun t => e.equiv (x.val t), fun t => by
        rw [e.target,e.source]; exact x.property t⟩
      invFun y := ⟨fun t => e.equiv.symm (y.val t), fun t => by
        change (e.inverse.equiv (y.val t)).target =
          (e.inverse.equiv (y.val (t+1))).source
        rw [e.inverse.target,e.inverse.source]; exact y.property t⟩
      left_inv x := by apply Subtype.ext; funext t; exact e.equiv.symm_apply_apply _
      right_inv y := by apply Subtype.ext; funext t; exact e.equiv.apply_symm_apply _ }
  step _ := rfl

private abbrev ParallelPerm {n : ℕ} (A : CountMat n n) :=
  (ij : Fin n × Fin n) → Equiv.Perm (Fin (A ij.1 ij.2))

private def parallelCoding {n : ℕ} {A : CountMat n n} (σ : ParallelPerm A) :
    EdgeCoding A A where
  equiv :=
    { toFun a := ⟨a.source,a.target,σ (a.source,a.target) a.number⟩
      invFun a := ⟨a.source,a.target,(σ (a.source,a.target)).symm a.number⟩
      left_inv a := by cases a; simp
      right_inv a := by cases a; simp }
  source _ := rfl
  target _ := rfl

private theorem parallelCoding_one {n : ℕ} (A : CountMat n n) :
    (parallelCoding (1 : ParallelPerm A)).path = PathCoding.identity A := by
  apply pathCoding_ext
  intro x
  apply Subtype.ext
  funext t
  cases x.val t
  rfl

/- Perm multiplication is function composition, hence σ*τ acts by τ then σ. -/
private theorem parallelCoding_mul {n : ℕ} {A : CountMat n n} (σ τ : ParallelPerm A) :
    (parallelCoding (σ*τ)).path = (parallelCoding τ).path.trans (parallelCoding σ).path := by
  apply pathCoding_ext
  intro x
  rfl

private def oneFiber {n : ℕ} {A : CountMat n n} (ij : Fin n × Fin n)
    (π : Equiv.Perm (Fin (A ij.1 ij.2))) : ParallelPerm A :=
  Function.update 1 ij π

private theorem oneFiber_one {n : ℕ} {A : CountMat n n} (ij : Fin n × Fin n) :
    oneFiber (A := A) ij 1 = 1 := by
  classical
  funext kl
  by_cases h : kl = ij
  · subst kl; simp [oneFiber]
  · simp [oneFiber,h]

private theorem oneFiber_mul {n : ℕ} {A : CountMat n n} (ij : Fin n × Fin n)
    (π τ : Equiv.Perm (Fin (A ij.1 ij.2))) :
    oneFiber ij (π*τ) = oneFiber (A := A) ij π * oneFiber ij τ := by
  classical
  funext kl
  by_cases h : kl = ij
  · subst kl; simp [oneFiber]
  · simp [oneFiber,h]

private theorem oneFiber_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (ij : Fin n × Fin n)
    (π : Equiv.Perm (Fin (A ij.1 ij.2))) :
    pathGyrationThree hd (parallelCoding (oneFiber ij π)).path = 0 := by
  classical
  induction π using Equiv.Perm.swap_induction_on with
  | one => rw [oneFiber_one,parallelCoding_one,pathGyrationThree_identity]
  | swap_mul π a b _ ih =>
    rw [oneFiber_mul,parallelCoding_mul,pathGyrationThree_then,ih,zero_add]
    apply pathGyrationThree_involution
    intro x
    apply Subtype.ext
    funext t
    apply edge_eq_coordinates
    · rfl
    · rfl
    change ((oneFiber ij (Equiv.swap a b) ((x.val t).source,(x.val t).target))
      (oneFiber ij (Equiv.swap a b) ((x.val t).source,(x.val t).target)
        (x.val t).number)).val = (x.val t).number.val
    generalize x.val t = edge
    rcases edge with ⟨i,j,k⟩
    by_cases h : (i,j) = ij
    · subst ij; simp [oneFiber]
    · simp [oneFiber,h]

/- A finite induction over the ACTUAL family of endpoint fibers, and swap
   induction inside each fiber. No generation/vanishing hypothesis is retained. -/
private theorem parallelCoding_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (σ : ParallelPerm A) :
    pathGyrationThree hd (parallelCoding σ).path = 0 := by
  classical
  have go : ∀ s : Finset (Fin n × Fin n), ∀ τ : ParallelPerm A,
      (∀ ij, ij ∉ s → τ ij = 1) →
      pathGyrationThree hd (parallelCoding τ).path = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro τ hτ
      have he : τ = 1 := funext (fun ij => hτ ij (by simp))
      rw [he,parallelCoding_one,pathGyrationThree_identity]
    | @insert ij s _ ih =>
      intro τ hτ
      let υ : ParallelPerm A := Function.update τ ij 1
      have hυ : ∀ kl, kl ∉ s → υ kl = 1 := by
        intro kl hkl
        by_cases h : kl = ij
        · subst kl; simp [υ]
        · simpa [υ,h] using hτ kl (by simp [h,hkl])
      have hfactor : τ = oneFiber ij (τ ij) * υ := by
        funext kl
        by_cases h : kl = ij
        · subst kl; simp [oneFiber,υ]
        · simp [oneFiber,υ,h]
      rw [hfactor,parallelCoding_mul,pathGyrationThree_then,
        ih υ hυ,oneFiber_three_zero,add_zero]
  exact go Finset.univ σ (by simp)

/- Every endpoint-preserving edge equivalence really is such a family.
   The finite bijection proof includes zero-size fibers. -/
private def EdgeCoding.family {n : ℕ} {A : CountMat n n} (e : EdgeCoding A A) :
    ParallelPerm A := fun ij => by
  classical
  let f : Fin (A ij.1 ij.2) → Fin (A ij.1 ij.2) := fun k =>
    ⟨(e.equiv ⟨ij.1,ij.2,k⟩).number.val, by
      simpa only [e.source,e.target] using (e.equiv ⟨ij.1,ij.2,k⟩).number.isLt⟩
  have hi : Function.Injective f := by
    intro k l h
    have he : e.equiv ⟨ij.1,ij.2,k⟩ = e.equiv ⟨ij.1,ij.2,l⟩ :=
      edge_eq_coordinates
        (a := e.equiv ⟨ij.1,ij.2,k⟩) (b := e.equiv ⟨ij.1,ij.2,l⟩)
        ((e.source ⟨ij.1,ij.2,k⟩).trans (e.source ⟨ij.1,ij.2,l⟩).symm)
        ((e.target ⟨ij.1,ij.2,k⟩).trans (e.target ⟨ij.1,ij.2,l⟩).symm) (congrArg Fin.val h)
    have hk := e.equiv.injective he
    exact Fin.ext (congrArg (fun a : Edge A => a.number.val) hk)
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi,rfl⟩)

private theorem edgeCoding_family_path {n : ℕ} {A : CountMat n n} (e : EdgeCoding A A) :
    (parallelCoding e.family).path = e.path := by
  apply pathCoding_ext
  intro x
  apply Subtype.ext
  funext t
  apply edge_eq_coordinates
  · exact (e.source (x.val t)).symm
  · exact (e.target (x.val t)).symm
  · rfl

private theorem edgeCoding_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (e : EdgeCoding A A) :
    pathGyrationThree hd e.path = 0 := by
  rw [← edgeCoding_family_path]
  exact parallelCoding_three_zero hd e.family

/-- Endpoint-preserving edge permutations have zero total forward offset modulo
three on the original canonical path basis. The supplied primitive equivalence
must be the literal coordinatewise action of that same edge permutation. -/
theorem parallel_edge_offset_sum_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (e : Edge A ≃ Edge A)
    (hs : ∀ a, (e a).source = a.source)
    (ht : ∀ a, (e a).target = a.target)
    (u : PrimitivePath A d ≃ PrimitivePath A d)
    (hu : ∀ x t, (u x).val.val t = e (x.val.val t)) :
    ZMod.castHom hd (ZMod 3)
      (∑ b : PathBasis A d, ZMod.finEquiv d (canonicalForwardOffset (u b.val))) = 0 := by
  let c : EdgeCoding A A := ⟨e, hs, ht⟩
  have he (x : PrimitivePath A d) : u x = c.path.primitive x := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact hu x t
  simp_rw [he]
  rw [← pathGyration_basis]
  exact edgeCoding_three_zero hd c

/- Explicit matrix-equality casts. Associators below are NOT identified with
   these casts: their discrepancy is a finite parallel-edge relabeling. -/
private def matrixCast {n : ℕ} {A B : CountMat n n} (h : A = B) : EdgeCoding A B := by
  subst B
  exact ⟨Equiv.refl _,fun _ => rfl,fun _ => rfl⟩

private theorem matrixCast_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A B : CountMat n n} (h : A = B) :
    pathGyrationThree hd (matrixCast h).path = 0 := by
  subst B
  exact pathGyrationThree_identity hd A

private theorem edgeCoding_three_zero_of_eq {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A B : CountMat n n} (h : A = B) (e : EdgeCoding A B) :
    pathGyrationThree hd e.path = 0 := by
  let ρ : EdgeCoding A A := e.trans (matrixCast h).inverse
  have he : ρ.path.trans (matrixCast h).path = e.path := by
    apply pathCoding_ext
    intro x
    apply Subtype.ext
    funext t
    exact (matrixCast h).equiv.apply_symm_apply _
  have ht := pathGyrationThree_then hd ρ.path (matrixCast h).path
  rw [he,edgeCoding_three_zero hd ρ,matrixCast_three_zero hd h,add_zero] at ht
  exact ht

/- Reassociate the three actual half-edges by split and join. The inverse
   equations use the canonical numbering inverses, including empty fibers. -/
private def associateEdge {n m p : ℕ} (R : CountMat n m) (U : CountMat m p)
    (V : CountMat p n) (e : Edge ((R*U)*V)) : Edge (R*(U*V)) :=
  let ab := (split (R*U) V e).1
  let c := (split (R*U) V e).2
  let a := (split R U ab).1
  let b := (split R U ab).2
  let hbc : b.target = c.source :=
    (split_target R U ab).trans (split_middle (R*U) V e)
  join R (U*V) a (join U V b c hbc) (split_middle R U ab)

private def unassociateEdge {n m p : ℕ} (R : CountMat n m) (U : CountMat m p)
    (V : CountMat p n) (e : Edge (R*(U*V))) : Edge ((R*U)*V) :=
  let a := (split R (U*V) e).1
  let bc := (split R (U*V) e).2
  let b := (split U V bc).1
  let c := (split U V bc).2
  let hab : a.target = b.source :=
    (split_middle R (U*V) e).trans (split_source U V bc).symm
  join (R*U) V (join R U a b hab) c (split_middle U V bc)

private def associator {n m p : ℕ} (R : CountMat n m) (U : CountMat m p)
    (V : CountMat p n) : EdgeCoding ((R*U)*V) (R*(U*V)) where
  equiv :=
    { toFun := associateEdge R U V
      invFun := unassociateEdge R U V
      left_inv e := by
        simp only [associateEdge,unassociateEdge,split_join,join_split]
      right_inv e := by
        simp only [associateEdge,unassociateEdge,split_join,join_split] }
  source _ := rfl
  target _ := rfl

private theorem associator_join {n m p : ℕ} (R : CountMat n m) (U : CountMat m p)
    (V : CountMat p n) (a : Edge R) (b : Edge U) (c : Edge V)
    (hab : a.target = b.source) (hbc : b.target = c.source) :
    (associator R U V).equiv
      (join (R*U) V (join R U a b hab) c hbc) =
      join R (U*V) a (join U V b c hbc) hab := by
  change associateEdge R U V _ = _
  simp only [associateEdge,split_join]

private theorem associator_three_zero {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R : CountMat n m) (U : CountMat m p) (V : CountMat p n) :
    pathGyrationThree hd (associator R U V).path = 0 :=
  edgeCoding_three_zero_of_eq hd (Matrix.mul_assoc R U V) (associator R U V)

/- An exact decomposition of each source edge into the three canonical split
   halves. This is used at both t and t+1 in the recoding diagram. -/
private theorem edge_three_decompose {n m p : ℕ} (R : CountMat n m) (U : CountMat m p)
    (V : CountMat p n) (e : Edge ((R * U) * V)) :
    ∃ (a : Edge R) (b : Edge U) (c : Edge V)
      (hab : a.target = b.source) (hbc : b.target = c.source),
      e = join (R*U) V (join R U a b hab) c hbc := by
  let ab := (split (R*U) V e).1
  let c := (split (R*U) V e).2
  let a := (split R U ab).1
  let b := (split R U ab).2
  have hab : a.target = b.source := split_middle R U ab
  have hbc : b.target = c.source :=
    (split_target R U ab).trans (split_middle (R*U) V e)
  have habjoin : join R U a b hab = ab := join_split R U ab
  refine ⟨a,b,c,hab,hbc,?_⟩
  simpa only [habjoin] using (join_split (R*U) V e).symm

/- The actual triangle, including ALL three numbering associators. The formula
   is aC ∘ c2 ∘ aB ∘ c1 ∘ aA = c3, not c2 ∘ c1 = c3. -/
private theorem recoding_triangle_diagram {n m p : ℕ} (R : CountMat n m)
    (U : CountMat m p) (V : CountMat p n) :
    ((((associator R U V).path.trans (elementaryCoding R (U*V))).trans
        (associator U V R).path).trans (elementaryCoding U (V*R))).trans
        (associator V R U).path = elementaryCoding (R*U) V := by
  apply pathCoding_ext
  intro x
  apply Subtype.ext
  funext t
  obtain ⟨a,b,c,hab,hbc,he⟩ := edge_three_decompose R U V (x.val t)
  obtain ⟨a',b',c',hab',hbc',he'⟩ := edge_three_decompose R U V (x.val (t+1))
  obtain ⟨a'',b'',c'',hab'',hbc'',he''⟩ :=
    edge_three_decompose R U V (x.val ((t+1)+1))
  have hca : c.target = a'.source := by
    simpa only [he,he',join] using x.property t
  change
    (associator V R U).equiv
      ((elementaryHomeomorph U (V*R)
        ((associator U V R).path.equiv
          (elementaryHomeomorph R (U*V) ((associator R U V).path.equiv x)))).val t) =
    (elementaryHomeomorph (R*U) V x).val t
  simp only [EdgeCoding.path,Equiv.coe_fn_mk,elementary_coordinate,he,he',he'',
    associator_join,split_join]

/-- The actual positive RS triangle in every period divisible by three,
    after reduction to ZMod 3. Empty vertex sets and zero entries are included. -/
theorem relativeForwardGyration_positive_triangle_mod_three
    {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R₁ : CountMat n m) (R₂ : CountMat m p) (S₃ : CountMat p n) :
    ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) R₁ (R₂*S₃)) +
      ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) R₂ (S₃*R₁)) =
    ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) (R₁*R₂) S₃) := by
  have ht := congrArg (fun f => pathGyrationThree (d := d) hd f)
    (recoding_triangle_diagram R₁ R₂ S₃)
  simp only [pathGyrationThree_then,associator_three_zero,zero_add,add_zero] at ht
  unfold pathGyrationThree at ht
  convert ht using 1 <;> rfl


end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
