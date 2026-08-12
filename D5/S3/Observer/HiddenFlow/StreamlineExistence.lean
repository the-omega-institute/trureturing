/- GID: D5/S3/Observer/HiddenFlow/StreamlineExistence
   generality: I
   mirror-B: D5/B/S3/Observer/HiddenFlow/StreamlineExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical solenoid streamline data instantiate the frozen observer
     decomposition with constant throat. -/

import D5.S1.Solenoid.StreamlineDecomposition
import D5.S3.Factorization.SolenoidProfiniteKernel
import D5.S3.Observer.StreamlineTheorem

namespace D5.S3.Observer.HiddenFlow.StreamlineExistence

open Set
open D5.S1.Dynamics
open D5.S3.Factorization.ProfinitePrimeDecomposition
open D5.S3.Factorization.SolenoidProfiniteKernel
open D5.S3.Observer.StreamlineTheorem

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private instance : Zero ProfiniteIntegers :=
  ⟨⟨fun _ => 0, by intro m n _; simp⟩⟩

private instance : Add ProfiniteIntegers :=
  ⟨fun x y => ⟨x.1 + y.1, by
    intro m n h
    change (ZMod.castHom h (ZMod m.1)) (x.1 n + y.1 n) =
      x.1 m + y.1 m
    rw [map_add]
    exact congrArg₂ (· + ·) (x.2 m n h) (y.2 m n h)⟩⟩

private instance : Neg ProfiniteIntegers :=
  ⟨fun x => ⟨-x.1, by
    intro m n h
    change (ZMod.castHom h (ZMod m.1)) (-x.1 n) = -x.1 m
    rw [map_neg]
    exact congrArg Neg.neg (x.2 m n h)⟩⟩

private instance : AddCommGroup ProfiniteIntegers where
  add := (· + ·)
  add_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  zero := 0
  zero_add _ := Subtype.ext (zero_add _)
  add_zero _ := Subtype.ext (add_zero _)
  neg := Neg.neg
  neg_add_cancel _ := Subtype.ext (neg_add_cancel _)
  add_comm _ _ := Subtype.ext (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def components (x : HiddenAddress) (m : ℕ+) :
    ∀ q : m.1.primeFactors, ZMod (q.1 ^ m.1.factorization q.1) := fun q =>
  let hp := Nat.prime_of_mem_primeFactors q.2
  letI : Fact q.1.Prime := ⟨hp⟩
  PadicInt.toZModPow (m.1.factorization q.1) (x ⟨q.1, hp⟩)

private theorem equivPi_assemble (x : HiddenAddress) (m : ℕ+) :
    (ZMod.equivPi m.1 m.2.ne') ((assemble x).1 m) = components x m := by
  change (ZMod.equivPi m.1 m.2.ne')
      ((ZMod.equivPi m.1 m.2.ne').symm (components x m)) = components x m
  exact (ZMod.equivPi m.1 m.2.ne').apply_symm_apply (components x m)

private theorem assemble_add (x y : HiddenAddress) :
    assemble (x + y) = assemble x + assemble y := by
  apply Subtype.ext
  funext m
  apply (ZMod.equivPi m.1 m.2.ne').injective
  calc
    (ZMod.equivPi m.1 m.2.ne') ((assemble (x + y)).1 m) =
        components (x + y) m := equivPi_assemble (x + y) m
    _ = components x m + components y m := by
      funext q
      simp [components]
    _ = (ZMod.equivPi m.1 m.2.ne') ((assemble x).1 m) +
          (ZMod.equivPi m.1 m.2.ne') ((assemble y).1 m) :=
      congrArg₂ (fun a b => a + b)
        (equivPi_assemble x m).symm (equivPi_assemble y m).symm
    _ = (ZMod.equivPi m.1 m.2.ne')
          ((assemble x).1 m + (assemble y).1 m) :=
      (map_add (ZMod.equivPi m.1 m.2.ne') _ _).symm

private noncomputable def profinitePrimeAddEquiv :
    HiddenAddress ≃+ ProfiniteIntegers where
  toEquiv := profinitePrimeEquiv.symm
  map_add' := assemble_add

private noncomputable def residueKernelAddEquiv :
    ProfiniteIntegers ≃+ UniversalSolenoid.projection.ker where
  toEquiv := kernelResidueEquiv.symm
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    funext m
    change ZMod.toAddCircle ((x + y).1 m) =
      ZMod.toAddCircle (x.1 m) + ZMod.toAddCircle (y.1 m)
    exact map_add ZMod.toAddCircle (x.1 m) (y.1 m)

/-- The repository's prime-adic classification, upgraded to the canonical
additive coordinates required by the frozen observer structure. -/
noncomputable def hiddenKernelAddEquiv :
    HiddenAddress ≃+ UniversalSolenoid.projection.ker :=
  profinitePrimeAddEquiv.trans residueKernelAddEquiv

/-- Turn reconstructed normalized data into the frozen observer decomposition
structure. The visible lift acts on the solenoid itself through `realFlow`; the
canonical additive equivalence names the same hidden kernel in the frozen
prime-adic coordinates. -/
noncomputable def toFrozenDecomposition
    (path : C(ℝ, UniversalSolenoid))
    (data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker)
    (hReconstruct : ∀ t,
      path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1) :
    StreamlineDecomposition where
  path := path
  visibleLift := fun t => UniversalSolenoid.realFlow (data.1 t)
  sameVisible := by
    funext t
    change UniversalSolenoid.projection (path t) =
      UniversalSolenoid.projection (UniversalSolenoid.realFlow (data.1 t))
    rw [hReconstruct t, map_add, data.2.property, add_zero]
  hiddenEquiv := hiddenKernelAddEquiv

/-- The frozen decomposition constructed from a constant hidden offset has
exactly that offset as its throat component at every time. -/
theorem frozen_streamline_throat_component_constant
    (path : C(ℝ, UniversalSolenoid))
    (data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker)
    (hReconstruct : ∀ t,
      path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1) (t : ℝ) :
    throatComponent
        (toFrozenDecomposition path data hReconstruct) t =
      hiddenKernelAddEquiv.symm data.2 := by
  apply hiddenKernelAddEquiv.injective
  simp [throatComponent, kernelDifference, toFrozenDecomposition,
    hReconstruct t]

/-- Every continuous solenoid path has unique normalized reconstruction data,
and those data canonically instantiate the frozen observer decomposition with
a time-independent throat component. Uniqueness is for the real lift and
hidden kernel element; the canonical additive equivalence fixes the frozen
structure's coordinate convention. -/
theorem existsUnique_frozen_streamline_decomposition
    (path : C(ℝ, UniversalSolenoid)) :
    ∃! data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker,
      data.1 0 =
          D5.S1.Solenoid.StreamlineDecomposition.baseRepresentative path 0 ∧
        ∃ hReconstruct : ∀ t,
            path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1,
          ∀ t, throatComponent
              (toFrozenDecomposition path data hReconstruct) t =
            hiddenKernelAddEquiv.symm data.2 := by
  rcases D5.S1.Solenoid.StreamlineDecomposition.existsUnique_normalized_streamline
      path 0 with ⟨data, hdata, hdataUnique⟩
  refine ⟨data, ⟨hdata.1, hdata.2, ?_⟩, ?_⟩
  · exact frozen_streamline_throat_component_constant
      path data hdata.2
  · intro other hother
    exact hdataUnique other ⟨hother.1, hother.2.choose⟩

/-- The constant throat component of the constructed frozen decomposition is
continuous. This is the earlier frozen streamline theorem applied after the
new existence construction supplies its missing input data. -/
theorem frozen_streamline_throat_component_continuous
    (path : C(ℝ, UniversalSolenoid))
    (data : C(ℝ, ℝ) × UniversalSolenoid.projection.ker)
    (hReconstruct : ∀ t,
      path t = UniversalSolenoid.realFlow (data.1 t) + data.2.1) :
    Continuous (throatComponent
      (toFrozenDecomposition path data hReconstruct)) := by
  rw [← continuousOn_univ]
  apply (streamline_offset_continuous_iff_constant isPreconnected_univ
    (toFrozenDecomposition path data hReconstruct) 0 (by simp)).2
  intro t _
  rw [frozen_streamline_throat_component_constant,
    frozen_streamline_throat_component_constant]

end D5.S3.Observer.HiddenFlow.StreamlineExistence
