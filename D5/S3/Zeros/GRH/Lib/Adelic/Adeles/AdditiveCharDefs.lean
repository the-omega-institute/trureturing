/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Adeles.AdditiveCharDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Adeles/AdditiveCharDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.ValuationPair
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdeleTopology
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Self-duality of a number field in its adeles; strong approximation; Poisson inequality
(known result; see Lib.Adelic.Adeles.OneSidedPoisson).

This file: Standard additive character of the adeles; normalised Haar measures; topological
instances. -/

noncomputable section

open NumberField MeasureTheory Measure FourierTransform Algebra AddChar QuotientAddGroup


variable (E) [Field E] [NumberField E]

lemma fourierChar_eq_one {t} : 𝐞 t = 1 ↔ ∃ n : ℤ, t = n := Circle.exp_eq_one.trans (by field_simp)

/-- The number 2^{r₂}/√|disc E|: the volume of the integral finite adeles that gives the
quotient of the adeles by E total mass one. -/
def volÔ := 2 ^ InfinitePlace.nrComplexPlaces E / ‖discr E‖₊.sqrt

/-- The standard additive character of the finite adeles: ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for any
a in E with x − a integral. -/
def ψf : AddChar (𝔸f E) Circle := toAddMonoidHomEquiv.symm (.comp (((mk' _).comp (algebraMap E
  (𝔸f E))).liftOfSurjective (Quot.ind (exists_sub_mem_Ô · |>.imp fun _ ↦ .symm ∘ eq_iff_sub_mem.2))
  ⟨.mk' (𝐞 <| trace ℚ E ·) (by aesop (add simp map_add_eq_mul)), fun a _ ↦ fourierChar_eq_one.2 ⟨_,
  mod_cast (coe_trace_int ⟨a, by aesop⟩).symm⟩⟩) (mk' (Ô E).toAddSubgroup))

/-- The standard additive character of the adeles of E: the product of exp(−2πi ∑_w 2 Re x_w)
over the infinite places and ψ_f of the finite part. -/
def stdAddChar : AddChar (𝔸 E) Circle := ⟨fun x ↦ 𝐞 (-∑ w, 2 * (x.1 w).re) * ψf E x.2,
  by simp, by simp [mul_add, map_add_eq_mul]; grind⟩

variable {E n} (w : FinPlace E) [Fintype n] (J : Matrix n n ℂ)

instance : PolishSpace (U J) where

instance : LocallyCompactSpace (U J) := inferInstance

instance : MeasureSpace (LocField w) := ⟨addHaarMeasure ⟨⟨_, isCompact_LocInt w⟩,
  (Valued.isOpen_integer _).interior_eq.substr (by simp)⟩⟩

instance : IsAddHaarMeasure (@volume (LocField w) _) := isAddHaarMeasure_addHaarMeasure _

@[simp] lemma volume_LocInt : @volume (LocField w) _ (LocInt w) = 1 := addHaarMeasure_self

@[simp] lemma volÔ_ne_zero : volÔ E ≠ 0 := by simp [volÔ, discr_ne_zero]

instance : MeasureSpace (𝔸f E) :=
  ⟨volÔ E • addHaarMeasure ⟨⟨_, isCompact_Ô⟩, by simp [isOpen_Ô.interior_eq]⟩⟩

instance : IsAddHaarMeasure (@volume (𝔸f E) _) := .nnreal_smul _ (by simp)

/-- For the chosen Haar measure on the finite adeles of E, the ring Ô of integral finite adeles
has volume 2^{r₂}/√|disc E|. -/
@[simp] lemma volume_Ô : volume (SetLike.coe (Ô E)) = volÔ E :=
  (congrArg _ addHaarMeasure_self).trans (mul_one _)

lemma ψf_eq (a : E) : ψf E a = 𝐞 (trace ℚ E a) := by
  simp [ψf]; erw [AddMonoidHom.liftOfRightInverse_comp_apply]; rfl

lemma ψf_of_mem {x} (h : x ∈ Ô E) : ψf E x = 1 := by simp [ψf, (eq_zero_iff _).2, h]

instance : SigmaFinite (@volume (𝔸f E) _) := inferInstance

deriving instance SecondCountableTopology, T2Space for 𝔸f E, 𝔸 E

deriving instance PolishSpace, LocallyCompactSpace, BorelSpace, IsTopologicalRing,
  MeasurableSingletonClass for 𝔸 E

instance : SigmaFinite (@volume (𝔸 E) _) := inferInstance

instance isAddHaarMeasure_𝔸 : IsAddHaarMeasure (@volume (𝔸 E) _) := prod.instIsAddHaarMeasure ..
