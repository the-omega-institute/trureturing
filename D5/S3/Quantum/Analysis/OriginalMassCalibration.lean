/- GID: D5/S3/Quantum/Analysis/OriginalMassCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/OriginalMassCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original readout used twice fixes the first mass scale and the remaining calibration. -/

import D5.S3.Quantum.Analysis.AsynchronousMassRigidity
import D5.S3.Quantum.Analysis.ProperConeMassBase

/-! # The same original readout and the two actual mass tensors -/

namespace D5.S3.Quantum.OriginalMassCalibration

open Function Set
open scoped BigOperators

variable {A D E : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The only supplied preparation and readout; K, M and Q are all derived using this same p. -/
structure OriginalData where
  L : D →ₗ[ℝ] A →ₗ[ℝ] E
  p : E →ₗ[ℝ] D
  omega : D

namespace OriginalData

variable (data : OriginalData (A := A) (D := D) (E := E))

def K (a : A) : D := data.p (data.L data.omega a)

def M (a b : A) : D := data.p (data.L (data.K a) b)

def Q (a b c : A) : E := data.L (data.M a b) c

private def massTwo (uD : Module.Dual ℝ D) :
    MultilinearMap ℝ (fun _ : Fin 2 => A) ℝ where
  toFun a := uD (data.M (a 0) (a 1))
  map_update_add' := by
    intro a i x y
    fin_cases i <;> simp [M, K, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro a i r x
    fin_cases i <;> simp [M, K, map_smul, LinearMap.smul_apply, smul_eq_mul]

private def massThree (uE : Module.Dual ℝ E) :
    MultilinearMap ℝ (fun _ : Fin 3 => A) ℝ where
  toFun a := uE (data.Q (a 0) (a 1) (a 2))
  map_update_add' := by
    intro a i x y
    fin_cases i <;> simp [Q, M, K, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro a i r x
    fin_cases i <;> simp [Q, M, K, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem mass_nonneg (C : ProperCone ℝ D) (u : Module.Dual ℝ D)
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) {x : D} (hx : x ∈ C) : 0 ≤ u x := by
  by_cases hz : x = 0
  · simp [hz]
  · exact (hu x hx hz).le

/-- Real spanning of the actual M and L implies real spanning of the actual Q=L(M,-).
No claim of generation of the positive joint cone by positive products is made. -/
theorem original_Q_spans
    (hspanM : Submodule.span ℝ (Set.range fun ab : A × A => data.M ab.1 ab.2) = ⊤)
    (hspanL : Submodule.span ℝ (Set.range fun dc : D × A => data.L dc.1 dc.2) = ⊤) :
    Submodule.span ℝ
      (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2) = ⊤ := by
  let W := Submodule.span ℝ
    (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2)
  have hL : ∀ d c, data.L d c ∈ W := by
    intro d c
    have hd : d ∈ Submodule.span ℝ
        (Set.range fun ab : A × A => data.M ab.1 ab.2) := by rw [hspanM]; trivial
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hd
      exact Submodule.subset_span ⟨(a, b, c), rfl⟩
    | zero => simp
    | add x y hx hy hx0 hy0 =>
      simpa only [map_add, LinearMap.add_apply] using W.add_mem hx0 hy0
    | smul r x hx hx0 =>
      simpa only [map_smul, LinearMap.smul_apply] using W.smul_mem r hx0
  apply top_le_iff.mp
  rw [← hspanL]
  exact Submodule.span_le.mpr (by rintro z ⟨⟨d, c⟩, rfl⟩; exact hL d c)

/-- Source Corollary 79.4 on the same original L,p,omega, over arbitrary nonzero finite
real proper-cone spaces: both actual mass tensors factor with strictly positive constants.
The input identities are required on the entire positive cone, including zero and unequal mass. -/
theorem original_mass_factorization [Nontrivial A] [Nontrivial D] [Nontrivial E]
    (CA : ProperCone ℝ A) (CD : ProperCone ℝ D) (CE : ProperCone ℝ E)
    (uA : Module.Dual ℝ A) (uD : Module.Dual ℝ D) (uE : Module.Dual ℝ E)
    (hgenA : Submodule.span ℝ (CA : Set A) = ⊤)
    (hgenD : Submodule.span ℝ (CD : Set D) = ⊤)
    (hgenE : Submodule.span ℝ (CE : Set E) = ⊤)
    (hposA : ∀ x ∈ CA, x ≠ 0 → 0 < uA x)
    (hposD : ∀ x ∈ CD, x ≠ 0 → 0 < uD x)
    (hposE : ∀ x ∈ CE, x ≠ 0 → 0 < uE x)
    (hLpos : ∀ d ∈ CD, ∀ a ∈ CA, data.L d a ∈ CE)
    (hppos : ∀ z ∈ CE, data.p z ∈ CD) (homega : data.omega ∈ CD)
    (hspanM : Submodule.span ℝ (Set.range fun ab : A × A => data.M ab.1 ab.2) = ⊤)
    (hspanL : Submodule.span ℝ (Set.range fun dc : D × A => data.L dc.1 dc.2) = ⊤)
    (Phi : A →ₗ[ℝ] A) (hPhiPos : ∀ a ∈ CA, Phi a ∈ CA)
    (hPhiMass : uA.comp Phi = uA)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • uA)
    (t s : ℝ) (ht : 0 < t) (ht1 : t < 1) (hs : 0 < s) (hs1 : s < 1)
    (hTwo : ∀ a ∈ CA, ∀ b ∈ CA, uD (data.M a b) =
      t * uD (data.M (Phi a) b) + (1-t) * uD (data.M a (Phi b)))
    (hThree : ∀ a ∈ CA, ∀ b ∈ CA, ∀ c ∈ CA, uE (data.Q a b c) =
      (s*t) * uE (data.Q (Phi a) b c) + (s*(1-t)) * uE (data.Q a (Phi b) c) +
        (1-s) * uE (data.Q a b (Phi c))) :
    ∃ lambda kappa : ℝ, 0 < lambda ∧ 0 < kappa ∧
      (∀ a b, uD (data.M a b) = lambda * uA a * uA b) ∧
      (∀ a b c, uE (data.Q a b c) = kappa * uA a * uA b * uA c) := by
  classical
  obtain ⟨hne, hcompact, hconv, hspan⟩ :=
    ProperConeMassBase.entire_base_geometry CA uA hgenA hposA
  let K := ProperConeMassBase.base CA uA
  have hinv : MapsTo Phi K K := by
    intro a ha
    exact ⟨hPhiPos a ha.1, (congrArg (fun f : Module.Dual ℝ A => f a) hPhiMass).trans ha.2⟩
  have hnorm : ∀ a ∈ K, uA a = 1 := fun _ ha => ha.2
  let alpha : Fin 2 → ℝ := ![t, 1-t]
  have halpha : ∀ i, 0 < alpha i := by intro i; fin_cases i <;> simp [alpha] <;> linarith
  have halphasum : ∑ i, alpha i = 1 := by simp [alpha, Fin.sum_univ_two]
  have htwoH : ∀ a ∈ Set.pi Set.univ (fun _ : Fin 2 => K),
      data.massTwo uD a = ∑ i, alpha i * data.massTwo uD (update a i (Phi (a i))) := by
    intro a ha
    simpa [massTwo, alpha, Fin.sum_univ_two] using hTwo (a 0) (ha 0 trivial).1 (a 1) (ha 1 trivial).1
  obtain ⟨lambda, hl⟩ := AsynchronousMassRigidity.multilinear_mass_factorization
    Phi uA hPhiMass hdual hcompact hne hconv hspan hinv hnorm
    alpha halpha halphasum (data.massTwo uD) htwoH
  let beta : Fin 3 → ℝ := ![s*t, s*(1-t), 1-s]
  have hbeta : ∀ i, 0 < beta i := by
    intro i; fin_cases i <;> simp [beta] <;> positivity
  have hbetasum : ∑ i, beta i = 1 := by simp [beta, Fin.sum_univ_succ]; ring
  have hthreeH : ∀ a ∈ Set.pi Set.univ (fun _ : Fin 3 => K),
      data.massThree uE a = ∑ i, beta i * data.massThree uE (update a i (Phi (a i))) := by
    intro a ha
    simpa [massThree, beta, Fin.sum_univ_succ, add_assoc] using
      hThree (a 0) (ha 0 trivial).1 (a 1) (ha 1 trivial).1 (a 2) (ha 2 trivial).1
  obtain ⟨kappa, hk⟩ := AsynchronousMassRigidity.multilinear_mass_factorization
    Phi uA hPhiMass hdual hcompact hne hconv hspan hinv hnorm
    beta hbeta hbetasum (data.massThree uE) hthreeH
  have hmTwo : ∀ a b, uD (data.M a b) = lambda * uA a * uA b := by
    intro a b
    simpa [massTwo, Fin.prod_univ_two, mul_assoc] using hl ![a,b]
  have hmThree : ∀ a b c, uE (data.Q a b c) = kappa * uA a * uA b * uA c := by
    intro a b c
    simpa [massThree, Fin.prod_univ_succ, mul_assoc] using hk ![a,b,c]
  obtain ⟨sigma, hsigma⟩ := hne
  have hsigmaMass : uA sigma = 1 := hsigma.2
  have hMpos : data.M sigma sigma ∈ CD :=
    hppos _ (hLpos _ (hppos _ (hLpos _ homega _ hsigma.1)) _ hsigma.1)
  have hlNonneg : 0 ≤ lambda := by
    simpa [hmTwo, hsigmaMass] using mass_nonneg CD uD hposD hMpos
  have hkNonneg : 0 ≤ kappa := by
    have hQpos : data.Q sigma sigma sigma ∈ CE := hLpos _ hMpos _ hsigma.1
    have heNonneg : 0 ≤ uE (data.Q sigma sigma sigma) := by
      by_cases hz : data.Q sigma sigma sigma = 0
      · simp [hz]
      · exact (hposE _ hQpos hz).le
    simpa [hmThree, hsigmaMass] using heNonneg
  have huDne : uD ≠ 0 := by
    obtain ⟨⟨d, hd⟩, _⟩ := ProperConeMassBase.entire_base_geometry CD uD hgenD hposD
    intro hz
    simpa [hz] using hd.2
  have huEne : uE ≠ 0 := by
    obtain ⟨⟨z, hz⟩, _⟩ := ProperConeMassBase.entire_base_geometry CE uE hgenE hposE
    intro hzero
    simpa [hzero] using hz.2
  have hlNe : lambda ≠ 0 := by
    intro hz
    apply huDne
    apply LinearMap.ker_eq_top.mp
    apply top_le_iff.mp
    rw [← hspanM]
    apply Submodule.span_le.mpr
    rintro d ⟨⟨a,b⟩, rfl⟩
    simpa [hmTwo, hz]
  have hkNe : kappa ≠ 0 := by
    intro hz
    apply huEne
    apply LinearMap.ker_eq_top.mp
    apply top_le_iff.mp
    rw [← data.original_Q_spans hspanM hspanL]
    apply Submodule.span_le.mpr
    rintro z ⟨⟨a,b,c⟩, rfl⟩
    simpa [hmThree, hz]
  exact ⟨lambda, kappa, lt_of_le_of_ne hlNonneg hlNe.symm,
    lt_of_le_of_ne hkNonneg hkNe.symm, hmTwo, hmThree⟩

/-- Mass calibration from the factorized original tensors and the full real recovery law.
The first scale is derived, rather than assumed, by using the same p twice at omega. -/
theorem original_scale_rigidity (uA : Module.Dual ℝ A) (uD : Module.Dual ℝ D)
    (uE : Module.Dual ℝ E) (homega : uD data.omega = 1)
    (sigma : A) (hsigma : uA sigma = 1)
    (lambda kappa : ℝ) (hlambda : 0 < lambda) (hkappa : 0 < kappa)
    (hmTwo : ∀ a b, uD (data.M a b) = lambda * uA a * uA b)
    (hmThree : ∀ a b c, uE (data.Q a b c) = kappa * uA a * uA b * uA c)
    (hspanM : Submodule.span ℝ (Set.range fun ab : A × A => data.M ab.1 ab.2) = ⊤)
    (hspanQ : Submodule.span ℝ
      (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2) = ⊤)
    (hrecover : ∀ a b c, data.p (data.Q a b c) = uA a • data.M b c) :
    lambda = 1 ∧
      (∀ z, uD (data.p z) = kappa⁻¹ * uE z) ∧
      (∀ d c, uE (data.L d c) = kappa * uD d * uA c) ∧
      (∀ d c, uD (data.p (data.L d c)) = uD d * uA c) := by
  have hl0 := hlambda.ne'
  have hk0 := hkappa.ne'
  have hp : ∀ z, uD (data.p z) = (lambda / kappa) * uE z := by
    intro z
    have hz : z ∈ Submodule.span ℝ
        (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2) := by
      rw [hspanQ]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a, b, c⟩, rfl⟩ := hz
      rw [hrecover, map_smul, hmTwo, hmThree, smul_eq_mul]
      field_simp
      <;> ring
    | zero => simp
    | add x y hx hy hx0 hy0 => simp only [map_add, hx0, hy0]; ring
    | smul c x hx hx0 => simp only [map_smul, smul_eq_mul, hx0]; ring
  have hL : ∀ d c, uE (data.L d c) = (kappa / lambda) * uD d * uA c := by
    intro d c
    have hd : d ∈ Submodule.span ℝ
        (Set.range fun ab : A × A => data.M ab.1 ab.2) := by rw [hspanM]; trivial
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hd
      change uE (data.Q a b c) = _
      rw [hmThree, hmTwo]
      field_simp
      <;> ring
    | zero => simp
    | add x y hx hy hx0 hy0 => simp only [map_add, LinearMap.add_apply, hx0, hy0]; ring
    | smul r x hx hx0 => simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx0]; ring
  have hpl : ∀ d c, uD (data.p (data.L d c)) = uD d * uA c := by
    intro d c
    rw [hp, hL]
    field_simp
    <;> ring
  have hM : ∀ a b, uD (data.M a b) = uA a * uA b := by
    intro a b
    simp only [M, K, hpl, homega, one_mul]
  have hscale : lambda = 1 := by
    have h₁ := hmTwo sigma sigma
    have h₂ := hM sigma sigma
    simpa [hsigma] using h₁.symm.trans h₂
  refine ⟨hscale, ?_, ?_, hpl⟩
  · intro z; simpa [hscale, one_div] using hp z
  · intro d c; simpa [hscale] using hL d c

end OriginalData
end D5.S3.Quantum.OriginalMassCalibration
