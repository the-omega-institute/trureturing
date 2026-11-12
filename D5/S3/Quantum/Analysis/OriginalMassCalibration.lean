/- GID: D5/S3/Quantum/Analysis/OriginalMassCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/OriginalMassCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original readout used twice fixes the first mass scale and the remaining calibration. -/

import D5.S3.Quantum.Analysis.AsynchronousMassRigidity
import D5.S3.Quantum.Dynamics.BaseNormContraction

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
    MultilinearMap ℝ (fun _ : Fin 2 => A) ℝ :=
  MultilinearMap.mk' (fun a => uD (data.M (a 0) (a 1)))
    (by intro a i x y; fin_cases i <;> simp [M, K, map_add, LinearMap.add_apply])
    (by intro a i r x; fin_cases i <;>
      simp [M, K, map_smul, LinearMap.smul_apply, smul_eq_mul])

private def massThree (uE : Module.Dual ℝ E) :
    MultilinearMap ℝ (fun _ : Fin 3 => A) ℝ :=
  MultilinearMap.mk' (fun a => uE (data.Q (a 0) (a 1) (a 2)))
    (by intro a i x y; fin_cases i <;> simp [Q, M, K, map_add, LinearMap.add_apply])
    (by intro a i r x; fin_cases i <;>
      simp [Q, M, K, map_smul, LinearMap.smul_apply, smul_eq_mul])

/-- Real spanning of the actual M and L implies real spanning of the actual Q=L(M,-).
No claim of generation of the positive joint cone by positive products is made. -/
private theorem original_Q_spans
    (hspanM : Submodule.span ℝ (Set.range fun ab : A × A => data.M ab.1 ab.2) = ⊤)
    (hspanL : Submodule.span ℝ (Set.range fun dc : D × A => data.L dc.1 dc.2) = ⊤) :
    Submodule.span ℝ
      (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2) = ⊤ := by
  let W := Submodule.span ℝ
    (Set.range fun abc : A × A × A => data.Q abc.1 abc.2.1 abc.2.2)
  have hL : ∀ d c, data.L d c ∈ W := by
    intro d c
    have himage := (Submodule.image_span_subset (data.L.flip c)
      (Set.range fun ab : A × A => data.M ab.1 ab.2) W).2 (by
      intro d hd
      obtain ⟨⟨a, b⟩, rfl⟩ := hd
      exact Submodule.subset_span ⟨(a, b, c), rfl⟩)
    exact himage ⟨d, by rw [hspanM]; trivial, rfl⟩
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
    AsynchronousMassRigidity.entire_base_geometry CA uA hgenA hposA
  let K := Foundation.CircuitBalancedConfirmation.base CA.toPointedCone uA
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
    intro i
    fin_cases i
    · exact mul_pos hs ht
    · exact mul_pos hs (sub_pos.mpr ht1)
    · exact sub_pos.mpr hs1
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
    simpa [hmTwo, hsigmaMass] using
      Dynamics.BaseNormContraction.functional_nonneg_on_cone (CD : ConvexCone ℝ D) uD hposD hMpos
  have hkNonneg : 0 ≤ kappa := by
    have hQpos : data.Q sigma sigma sigma ∈ CE := hLpos _ hMpos _ hsigma.1
    have heNonneg : 0 ≤ uE (data.Q sigma sigma sigma) :=
      Dynamics.BaseNormContraction.functional_nonneg_on_cone (CE : ConvexCone ℝ E) uE hposE hQpos
    simpa [hmThree, hsigmaMass] using heNonneg
  have huDne : uD ≠ 0 := by
    obtain ⟨⟨d, hd⟩, _⟩ := AsynchronousMassRigidity.entire_base_geometry CD uD hgenD hposD
    intro hz
    simpa [hz] using hd.2
  have huEne : uE ≠ 0 := by
    obtain ⟨⟨z, hz⟩, _⟩ := AsynchronousMassRigidity.entire_base_geometry CE uE hgenE hposE
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
private theorem original_scale_rigidity (uA : Module.Dual ℝ A) (uD : Module.Dual ℝ D)
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
    have heq : uD.comp data.p = (lambda / kappa) • uE := by
      apply LinearMap.ext_on_range hspanQ
      rintro ⟨a, b, c⟩
      change uD (data.p (data.Q a b c)) = (lambda / kappa) * uE (data.Q a b c)
      rw [hrecover, map_smul, hmTwo, hmThree, smul_eq_mul]
      field_simp
      <;> ring
    intro z
    exact LinearMap.congr_fun heq z
  have hL : ∀ d c, uE (data.L d c) = (kappa / lambda) * uD d * uA c := by
    intro d c
    have heq : uE.comp (data.L.flip c) = ((kappa / lambda) * uA c) • uD := by
      apply LinearMap.ext_on_range hspanM
      rintro ⟨a, b⟩
      change uE (data.Q a b c) = ((kappa / lambda) * uA c) * uD (data.M a b)
      rw [hmThree, hmTwo]
      field_simp
      <;> ring
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_right_comm] using LinearMap.congr_fun heq d
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

/-- The actual mass laws imply calibration using the same p twice, provided the original
full real recovery law is available. No mass factorization is assumed. The derivation of
recovery from the remaining PRE clauses is a separate predecessor. -/
theorem original_mass_calibration [Nontrivial A] [Nontrivial D] [Nontrivial E]
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
        (1-s) * uE (data.Q a b (Phi c)))
    (homegaMass : uD data.omega = 1)
    (hrecover : ∀ a b c, data.p (data.Q a b c) = uA a • data.M b c) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (∀ a b, uD (data.M a b) = uA a * uA b) ∧
      (∀ a b c, uE (data.Q a b c) = kappa * uA a * uA b * uA c) ∧
      (∀ z, uD (data.p z) = kappa⁻¹ * uE z) ∧
      (∀ d c, uE (data.L d c) = kappa * uD d * uA c) ∧
      (∀ d c, uD (data.p (data.L d c)) = uD d * uA c) := by
  obtain ⟨lambda, kappa, hl, hk, hmTwo, hmThree⟩ := data.original_mass_factorization
    CA CD CE uA uD uE hgenA hgenD hgenE hposA hposD hposE hLpos hppos homega
    hspanM hspanL Phi hPhiPos hPhiMass hdual t s ht ht1 hs hs1 hTwo hThree
  obtain ⟨⟨sigma, hsigma⟩, _⟩ :=
    AsynchronousMassRigidity.entire_base_geometry CA uA hgenA hposA
  obtain ⟨hscale, hp, hL, hpl⟩ := data.original_scale_rigidity uA uD uE
    homegaMass sigma hsigma.2 lambda kappa hl hk hmTwo hmThree hspanM
    (data.original_Q_spans hspanM hspanL) hrecover
  exact ⟨kappa, hk, (by simpa only [hscale, one_mul] using hmTwo), hmThree, hp, hL, hpl⟩

end OriginalData

example : ∃ kappa : ℝ, 0 < kappa ∧
    ∀ a b c : ℝ, a * b * c = kappa * a * b * c := by
  let data : OriginalData (A := ℝ) (D := ℝ) (E := ℝ) :=
    ⟨LinearMap.mul ℝ ℝ, LinearMap.id, 1⟩
  let C := ProperCone.positive ℝ ℝ
  let u : Module.Dual ℝ ℝ := LinearMap.id
  have hg : Submodule.span ℝ (C : Set ℝ) = ⊤ := by
    apply top_unique
    intro x _
    have h1 : (1 : ℝ) ∈ Submodule.span ℝ (C : Set ℝ) :=
      Submodule.subset_span (by change 0 ≤ (1 : ℝ); norm_num)
    simpa using (Submodule.span ℝ (C : Set ℝ)).smul_mem x h1
  have hp : ∀ x ∈ C, x ≠ 0 → 0 < u x := by
    intro x hx hn
    exact lt_of_le_of_ne hx hn.symm
  have hM : Submodule.span ℝ (Set.range fun ab : ℝ × ℝ => data.M ab.1 ab.2) = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.subset_span
    exact ⟨(1, x), by simp [OriginalData.M, OriginalData.K, data]⟩
  have hL : Submodule.span ℝ (Set.range fun dc : ℝ × ℝ => data.L dc.1 dc.2) = ⊤ := by
    apply top_unique
    intro x _
    exact Submodule.subset_span ⟨(1, x), by simp [data]⟩
  have hdual : ∀ f : Module.Dual ℝ ℝ, f.comp LinearMap.id = f →
      ∃ c : ℝ, f = c • u := by
    intro f _
    refine ⟨f 1, ?_⟩
    ext x
    have he := f.map_smul x (1 : ℝ)
    simpa [u, smul_eq_mul, mul_comm] using he
  obtain ⟨kappa, hk, _, h3, _, _, _⟩ := data.original_mass_calibration
    C C C u u u hg hg hg hp hp hp
    (by intro d hd a ha; exact mul_nonneg hd ha)
    (by intro z hz; exact hz)
    (by change 0 ≤ (1 : ℝ); norm_num) hM hL
    LinearMap.id (by intro x hx; exact hx) rfl hdual
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro a _ b _; simp [OriginalData.M, OriginalData.K, data, u]; ring)
    (by intro a _ b _ c _; simp [OriginalData.Q, OriginalData.M, OriginalData.K, data, u]; ring)
    rfl
    (by intro a b c; simp [OriginalData.Q, OriginalData.M, OriginalData.K, data, u]; ring)
  refine ⟨kappa, hk, ?_⟩
  simpa [OriginalData.Q, OriginalData.M, OriginalData.K, data, u] using h3

end D5.S3.Quantum.OriginalMassCalibration
