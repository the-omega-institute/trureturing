/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracket
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Bilinear native current descent to relative ghost-one cohomology -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent

/-! The bilinear operation on the actual graded relative BRST quotients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GhostSpace GradedCycles GradedBoundaries GradedCohomology)
open private assocQ_reassoc mem_ghostSpace gradedBoundaryMap
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private N_reassoc from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local notation "Cycles" => GradedCycles planeFrame planeBasis
local notation "Coh" => GradedCohomology planeFrame planeBasis
local notation "Boundaries" => GradedBoundaries planeFrame planeBasis

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) (g : ℤ) : AddCommGroup (Cycles p g) :=
  Submodule.addCommGroup _

private theorem degree_shell (p : Charge hyperbolicPlane) (g : ℤ) (x : relativeShell p) :
    x ∈ GhostSpace p g ↔ Degree g (reassoc.symm x.val) := by
  rw [mem_ghostSpace]
  let y := reassoc.symm x.val
  have hy : reassoc y = x.val := reassoc.apply_symm_apply _
  change _ ↔ N y = _
  constructor
  · intro h
    apply reassoc.injective
    rw [N_reassoc, map_smul, hy]
    exact h
  · intro h
    have h' : reassoc (N y) = reassoc ((g : ℂ) • y) := congrArg reassoc h
    rw [N_reassoc, reassoc.map_smul, hy] at h'
    exact h'

private theorem closed_shell (p : Charge hyperbolicPlane) (x : relativeShell p) :
    relativeQ planeFrame planeBasis p x = 0 ↔ Q (reassoc.symm x.val) = 0 := by
  let y := reassoc.symm x.val
  have hy : reassoc y = x.val := reassoc.apply_symm_apply _
  have hQ : reassoc (Q y) = assocQ x.val :=
    (assocQ_reassoc y).symm.trans (congrArg assocQ hy)
  constructor
  · intro h
    have h' : assocQ x.val = 0 := congrArg Subtype.val h
    exact reassoc.injective (hQ.trans (h'.trans reassoc.map_zero.symm))
  · intro h
    apply Subtype.ext
    change assocQ x.val = 0
    exact hQ.symm.trans ((congrArg reassoc h).trans reassoc.map_zero)

abbrev nativeValue {p : Charge hyperbolicPlane} (x : Cycles p 1) : ComplexState :=
  reassoc.symm x.val.val

private theorem native_mem {p : Charge hyperbolicPlane} (x : Cycles p 1) :
    reassoc (nativeValue x) ∈ relativeShell p := by
  simpa only [nativeValue, reassoc.apply_symm_apply] using x.val.property

private theorem native_degree {p : Charge hyperbolicPlane} (x : Cycles p 1) :
    Degree 1 (nativeValue x) := (degree_shell p 1 x.val).mp x.property.1

private theorem native_closed {p : Charge hyperbolicPlane} (x : Cycles p 1) :
    Q (nativeValue x) = 0 := (closed_shell p x.val).mp x.property.2

private def cycleOf {p : Charge hyperbolicPlane} (x : ComplexState)
    (hx : reassoc x ∈ relativeShell p) (dx : Degree 1 x) (qx : Q x = 0) : Cycles p 1 :=
  ⟨⟨reassoc x, hx⟩,
    (degree_shell p 1 _).mpr (by simpa only [reassoc.symm_apply_apply] using dx),
    (closed_shell p _).mpr (by simpa only [reassoc.symm_apply_apply] using qx)⟩

private theorem nativeValue_injective (p : Charge hyperbolicPlane) :
    Function.Injective (nativeValue (p := p)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (reassoc.symm.injective h))

def cycleCurrent {p q : Charge hyperbolicPlane} (x : Cycles p 1) (y : Cycles q 1) :
    Cycles (p + q) 1 :=
  let h := current_closed (native_mem x) (native_mem y)
    (native_degree x) (native_degree y) (native_closed x) (native_closed y)
  cycleOf (current (nativeValue x) (nativeValue y)) h.1 h.2.1 h.2.2

private theorem native_cycleCurrent {p q : Charge hyperbolicPlane}
    (x : Cycles p 1) (y : Cycles q 1) :
    nativeValue (cycleCurrent x y) = current (nativeValue x) (nativeValue y) :=
  reassoc.symm_apply_apply _

private theorem native_boundary {p : Charge hyperbolicPlane}
    (a : GhostSpace p ((1 : ℤ) - 1)) :
    nativeValue (gradedBoundaryMap planeFrame planeBasis p 1 a) = Q (reassoc.symm a.val.val) := by
  apply reassoc.injective
  change reassoc (reassoc.symm (assocQ a.val.val)) = reassoc (Q (reassoc.symm a.val.val))
  rw [reassoc.apply_symm_apply, ← assocQ_reassoc, reassoc.apply_symm_apply]

private theorem boundary_of_native {p : Charge hyperbolicPlane} (x : Cycles p 1)
    (a : ComplexState) (ha : reassoc a ∈ relativeShell p) (da : Degree 0 a)
    (qa : Q a = nativeValue x) : x ∈ Boundaries p 1 := by
  let s : relativeShell p := ⟨reassoc a, ha⟩
  have d : s ∈ GhostSpace p ((1 : ℤ) - 1) :=
    (degree_shell p _ s).mpr (by simpa only [s, sub_self, reassoc.symm_apply_apply] using da)
  apply LinearMap.mem_range.mpr
  refine ⟨⟨s, d⟩, nativeValue_injective p ?_⟩
  simpa only [native_boundary, s, reassoc.symm_apply_apply] using qa

private theorem native_add {p : Charge hyperbolicPlane} (x y : Cycles p 1) :
    nativeValue (x + y) = nativeValue x + nativeValue y :=
  reassoc.symm.map_add x.val.val y.val.val

private theorem native_smul {p : Charge hyperbolicPlane} (c : ℂ) (x : Cycles p 1) :
    nativeValue (c • x) = c • nativeValue x :=
  reassoc.symm.map_smul c x.val.val

private def classCurrent (p q : Charge hyperbolicPlane) :
    Cycles p 1 →ₗ[ℂ] Cycles q 1 →ₗ[ℂ] Coh (p + q) 1 where
  toFun x := {
    toFun y := (Boundaries (p + q) 1).mkQ (cycleCurrent x y)
    map_add' y z := by
      rw [← map_add (Boundaries (p + q) 1).mkQ]
      apply congrArg (Boundaries (p + q) 1).mkQ
      apply nativeValue_injective
      rw [native_add, native_cycleCurrent, native_cycleCurrent, native_cycleCurrent, native_add]
      exact (current (nativeValue x)).map_add _ _
    map_smul' c y := by
      rw [← map_smul (Boundaries (p + q) 1).mkQ]
      apply congrArg (Boundaries (p + q) 1).mkQ
      apply nativeValue_injective
      rw [native_smul, native_cycleCurrent, native_cycleCurrent, native_smul]
      exact (current (nativeValue x)).map_smul c _ }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (Boundaries (p + q) 1).mkQ _ =
      (Boundaries (p + q) 1).mkQ _ + (Boundaries (p + q) 1).mkQ _
    rw [← map_add (Boundaries (p + q) 1).mkQ]
    apply congrArg (Boundaries (p + q) 1).mkQ
    apply nativeValue_injective
    rw [native_add, native_cycleCurrent, native_cycleCurrent, native_cycleCurrent, native_add]
    exact LinearMap.congr_fun (current.map_add (nativeValue x) (nativeValue y)) (nativeValue z)
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change (Boundaries (p + q) 1).mkQ _ = c • (Boundaries (p + q) 1).mkQ _
    rw [← map_smul (Boundaries (p + q) 1).mkQ]
    apply congrArg (Boundaries (p + q) 1).mkQ
    apply nativeValue_injective
    rw [native_smul, native_cycleCurrent, native_cycleCurrent, native_smul]
    exact LinearMap.congr_fun (current.map_smul c (nativeValue x)) (nativeValue y)

/-- Bilinear descent on the existing ghost-one kernel/image quotients at all momenta. -/
def bracket (p q : Charge hyperbolicPlane) :
    Coh p 1 →ₗ[ℂ] Coh q 1 →ₗ[ℂ] Coh (p + q) 1 :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (M := Cycles p 1) (N := Cycles q 1) (P := Coh (p + q) 1)
    (ρ := RingHom.id ℂ) (σ := RingHom.id ℂ) (Boundaries p 1) (Boundaries q 1)
    (classCurrent p q)
    (by
      intro x hx
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      change Submodule.Quotient.mk (cycleCurrent _ y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      let v := reassoc.symm a.val.val
      have ha : reassoc v ∈ relativeShell p := by
        simpa only [v, reassoc.apply_symm_apply] using a.val.property
      have da : Degree 0 v := by
        simpa only [sub_self] using (degree_shell p _ a.val).mp a.property
      obtain ⟨hs, ds, qs⟩ := left_boundary ha (native_mem y) da
        (native_degree y) (native_closed y)
      exact boundary_of_native _ _ hs ds (by rw [qs, native_cycleCurrent, native_boundary]))
    (by
      intro y hy
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      change Submodule.Quotient.mk (cycleCurrent x _) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      let v := reassoc.symm a.val.val
      have ha : reassoc v ∈ relativeShell q := by
        simpa only [v, reassoc.apply_symm_apply] using a.val.property
      have da : Degree 0 v := by
        simpa only [sub_self] using (degree_shell q _ a.val).mp a.property
      obtain ⟨hs, ds, qs⟩ := right_boundary (native_mem x) ha
        (native_degree x) da (native_closed x)
      exact boundary_of_native _ _ hs ds (by rw [qs, native_cycleCurrent, native_boundary]))

@[simp] theorem bracket_mk {p q : Charge hyperbolicPlane} (x : Cycles p 1) (y : Cycles q 1) :
    bracket p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (cycleCurrent x y) := rfl

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
