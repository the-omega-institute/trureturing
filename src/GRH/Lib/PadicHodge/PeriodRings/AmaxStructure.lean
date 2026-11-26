import GRH.Lib.PadicHodge.PeriodRings.ThetaKernel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Adic extension of linear maps; existence of (p,z)-adic topological bases with
coordinates. Subgroup of multiples of n in an abelian group; link with adic filtration. Separated
module of bounded rank with regular parameters over complete base is finite free. Coordinates of an
adic topological basis: approximation, submodule membership, separation. Colmez's A_max, B_max^+,
B_max with Frobenius, Galois action and θ. A_max modulo p is a polynomial ring; how A_inf lies in
A_max. -/

noncomputable section

section

attribute [-simp] sup_of_le_right sup_of_le_left

open Quot Ideal Submodule Finsupp AdicCompletion SModEq Function Module
variable {S F M} [CommRing S] [AddCommGroup F] [Module S F] [AddCommGroup M] [Module S M] {C}
  [AddCommGroup C] [Module S C] (I : Ideal S) [IsAdicComplete I C] (β : F →ₗ[S] M)

instance [IsPrecomplete I S] [Module.Finite S M] : IsPrecomplete I M :=
  of_surjective_iff.1 (by simpa using (ofTensorProduct_surjective_of_finite I M).comp (
    TensorProduct.mk_surjective _ M _ (of_surjective I S)) ·)

lemma isHausdorff_of_injective_pi [IsHausdorff I F] {ι} (f : M →ₗ[S] ι → F) (h :
  Injective f := by simp) : IsHausdorff
  I M := of_injective_iff.1 fun _ _ e ↦ h <| funext fun i ↦ of_inj.1 <|
  (map_of ..).symm.trans <| (congrArg (AdicCompletion.map I (.proj i ∘ₗ f)) e).trans (map_of ..)

lemma isAdicComplete_of_free [IsAdicComplete I S] [Free S M] [Module.Finite S M] : IsAdicComplete I
  M := {isHausdorff_of_injective_pi I _ (Free.chooseBasis ..).equivFun.injective with}

/-- Let C be I-adically complete, β: F → M have I-adically dense image, and g: F → C satisfy
g(f) ∈ I^n C whenever β(f) ∈ I^{2n} M. Then g = G ∘ β for some S-linear G: M → C. -/
lemma exists_adic_extension (g : F →ₗ[S] C) (h₁ : Surjective (mkQ (I • ⊤) ∘ₗ β)) (h₂ : ∀ n,
  comap β (I ^ (n + n) • ⊤) ≤ comap g (I ^ n • ⊤)) : ∃ G : M →ₗ[S] C, ∀ f, G (β f) = g f :=
  ⟨(ofLinearEquiv I _).symm.1 ∘ₗ (LinearMap.quotKerEquivOfSurjective _
  (map_surjective_of_mkQ_comp_surjective h₁)).congrLeft _ ℕ (liftQ _ (map I g) ((mk_surjective I
  F).forall.2 fun a h ↦ ext (((a.map I g).2 (by simp)).trans <| zero.2 <| h₂ · (zero.1
  congr($h.1 _) :)))) ∘ₗ of I _, by simp [← map_of, LinearEquiv.symm_apply_eq]⟩

attribute [local simp] Ideal.span_insert pow_succ' mul_smul sup_smul mem_sup span_smul_eq

lemma comap_span_pow_smul_le {a} (t : S) (k : comap β (span {a, t} • ⊤) ≤ span {a, t} • ⊤) (h : ∀ y
  w : M, a • w = t • y → t = 0 ∨ ∃ c, a • c = y) n : comap β (span {t ^ n, a} • ⊤) ≤ span {t ^ n, a}
  • ⊤ := by induction' n with n i <;> simp_all [top_sup_eq, LE.le, mem_singleton_set_smul, add_comm]
            exact fun x v u e ↦ (k _ _ e).elim fun u' ⟨c, _⟩ ↦ (h (β c - t ^ n • v) (u - β u')
              (by grind [smul_sub, map_smul])).rec (by bound) fun ⟨w, _⟩ ↦ (@i c v w (by grind)).imp
              fun _ ↦ .imp' (u' + t • ·) (by grind [smul_add, smul_comm])

/-- a topological basis of `M` over `S` with its coordinates -/
structure Lift.AdicBasis.{u} (M : Type u) [AddCommGroup M] [Module S M] where
  (Index : Type u) (b : Index → M) (coord : Index → M →ₗ[S] S)
  dense : Surjective (mkQ (I • ⊤) ∘ₗ linearCombination S b)
  dual i f : coord i (linearCombination S b f) = f i

/-- Let S be I-adically complete, I = (p, z) maximal, and M an S-module without p-torsion (or p
= 0) in which za ∈ pM implies a ∈ pM. Vectors independent modulo IM belong to an I-adic
topological basis of M with coordinates. -/
lemma Lift.exists_adicBasis {I p z} (hI : I = span {p, z}) [I.IsMaximal] [IsAdicComplete I S] (hz :
    ∀ a b : M, z • a = p • b → ∃ c, a = p • c) (t : Set M := ∅) (ht : LinearIndepOn (S ⧸ I) (I • ⊤ :
    Submodule S M).mkQ t := by simp) (hp : ∀ a : M, p • a = 0 → p = 0 ∨ a = 0 := by aesop) :
    ∃ c : AdicBasis I M, t ⊆ .range c.b := let := Quotient.field I
  by choose s _ _ hs li using exists_linearIndepOn_extension ht le_top
     use ⟨s, (↑), _, ?a, fun i ↦ (exists_adic_extension I _ (lapply i) ?a fun n x h ↦
    smul_top_le_comap_smul_top _ _
       (smul_mono_left ?_ (comap_span_pow_smul_le _ p (comap_span_pow_smul_le _ z
    (hI ▸ fun x ↦ by simpa [← submodule_top, ← submodule_smul, Quotient.eq_zero_iff_mem] using!
       linearIndependent_iff''.1 li _ (x ·) (by aesop) ∘ (map_sum (mkQ _) ..).symm.trans ∘ zero.2)
    (by grind) n) (n.rec (by simp) (by simp_intro n i y w e; cases hz _ _ e; grind [hp (y - z •
       ‹M›), smul_sub, smul_comm])) n (smul_mono_left ?_ h)))).choose_spec⟩, by simpa
     exact ind (by simpa [mem_span_iff_linearCombination] using!
       (restrictScalars_span S _ mk_surjective _).le <| hs ⟨·, ⟨⟩, rfl⟩)
     all_goals simp [*, ← span_singleton_pow, pow_right_mono, sup_pow_add_le_pow_sup_pow]

/-- The subgroup nX of an abelian group X, for a natural number n. -/
abbrev nsmulRange n X [AddCommGroup X] := (@nsmulAddMonoidHom X _ n).range

variable {X Y} {S : _} [AddCommGroup X] [AddCommGroup Y] [CommRing S] [Module S X] [Module S Y]

lemma nsmulRange.map_mem (f : X →ₗ[S] Y) {n x} : x ∈ nsmulRange n X →
  f x ∈ nsmulRange n Y := by aesop

lemma nsmulRange.mem_span_pow_smul_top_iff {p : ℕ} {k x} : x ∈ Ideal.span {(p : S)} ^ k • (⊤ :
  Submodule S X) ↔ x ∈ nsmulRange (p ^ k) X := by simp [Ideal.span_singleton_pow,
  Submodule.span_smul_eq, Submodule.mem_singleton_set_smul, ← Nat.cast_smul_eq_nsmul S, eq_comm]

end

/-- Let S be complete for a maximal ideal (p, z), and M a (p, z)-adically separated module with
p zero or injective on M, z injective on M/pM, and linearly independent families of bounded
size. Then M is free of finite rank. -/
lemma free_finite_of_rank_le {S M : Type} [CommRing S] [Nontrivial S] [AddCommGroup M] [Module S M]
    {I : Ideal S} {p z} (hI : I = .span {p, z}) [I.IsMaximal] [IsAdicComplete I S] (H : IsHausdorff
    I M) (hz : ∀ x y : M, z • x = p • y → ∃ w, x = p • w) (d : ℕ) (hd : Module.rank S M ≤ d)
    (hp : ∀ x : M, p • x = 0 → p = 0 ∨ x = 0 := by simp) : Module.Free S M ∧ Module.Finite S M :=
  let ⟨c, _⟩ := Lift.exists_adicBasis hI hz
  have li := linearIndependent_iff.2 (by simp_all [Finsupp.ext_iff, ← c.5])
  have := Cardinal.mk_lt_aleph0_iff.1 (by grw [li.cardinal_le_rank, hd]; simp)
  (fun e ↦ ⟨.of_equiv e, .equiv e⟩) (.ofBijective _ ⟨li, surjective_of_mkQ_comp_surjective c.4⟩)

namespace Lift.AdicBasis

open Finsupp Submodule AdicCompletion
variable {S A} [CommRing S] [AddCommGroup A] [Module S A] {I : Ideal S} (c : AdicBasis I A)

/-- For coordinates c on the S-module A, with vectors b_j and coordinate maps λ_i: if y − ∑ f_j
b_j lies in I^n A for a finitely supported family f, then λ_i(y) − f_i lies in I^n for every
i. -/
lemma coord_sub_mem_pow {n y f} (h : y - linearCombination S c.b f ∈ I ^ n • (⊤ : Submodule S A))
  i : c.coord i y - f i ∈ I ^ n := by simpa [dual] using smul_top_le_comap_smul_top _ (c.coord i) h

/-- For a topological basis (b_i) of A over S with coordinates λ_i, every y in A and n ≥ 0: for
all sufficiently large finite sets F of indices, y − Σ_{i∈F} λ_i(y) b_i lies in I^n A. -/
lemma eventually_sub_sum_mem y n : ∀ᶠ F in .atTop, y - ∑ i ∈ F,
  c.coord i y • c.b i ∈ I ^ n • (⊤ : Submodule S A) :=
  Filter.mem_atTop_sets.2 (((map_surjective_of_mkQ_comp_surjective c.dense).comp (mk_surjective I _)
  (of I A y)).imp' (· n |>.1) fun f e F hF ↦ have hf := SModEq.sub_mem.1 congr($e.1 n).symm
  (sub_mem_iff_right _ hf).1 (by simp [linearCombination_apply_of_mem_supported _ hF, sum_mem,
      ← F.sum_sub_distrib, ← sub_smul, smul_mem_smul, c.coord_sub_mem_pow hf]))

/-- If an S-submodule P of A contains I^n A and all terms λ_i(y) b_i, then it contains y. -/
lemma mem_of_coord {P : Submodule S A} {n y} (hP : I ^ n • ⊤ ≤ P) (h : ∀ i,
  c.coord i y • c.b i ∈ P) : y ∈ P := by grind [sum_mem, sub_mem_iff_left,
  hP (c.eventually_sub_sum_mem y n).exists.choose_spec]

lemma eq_zero_of_coord [H : IsHausdorff I A] {y} (h : ∀ i, c.coord i y = 0) :
    y = 0 := H.1 _ (by simp_all [SModEq, c.mem_of_coord le_rfl])

end Lift.AdicBasis

attribute [-simp] map_smul isUnit_map_iff map_eq_zero Nat.cast_eq_zero IsUnit.dvd mul_eq_zero

open Ideal Polynomial AdjoinRoot nonZeroDivisors Localization IsScalarTower algebraMap
variable {p} [ThePrime p] (m : FrobGal) (a : Ainf) {R S} [CommRing R] [CommRing S] [Algebra R S]

/-- The period ring A (Colmez's A_max): the p-adic completion of A_inf[X]/(pX − ξ). -/
def Amax := let A := AdjoinRoot (C p.cast * X - C xi); AdicCompletion (span {(p : A)}) A
deriving CommRing, Algebra Ainf, Algebra ℤ_[p], IsScalarTower ℤ_[p] Ainf

/-- The period ring B^+ = A[1/p], where A is `Amax`. -/
def BPlus := Away (p : Amax) deriving CommRing, Algebra Ainf, Algebra ℤ_[p], Algebra Amax,
  IsScalarTower ℤ_[p] Ainf, IsScalarTower Ainf Amax, IsScalarTower ℤ_[p] Amax

/-- The period ring B = B^+[1/μ] (Colmez's B_max), over which crystalline representations are
defined. -/
def Bcris := Away (algebraMap _ BPlus mu)

/-- The ring B_dR^+, defined as the completion of B^+ with respect to the ideal generated by the
image of ξ. -/
def BdRPlus := AdicCompletion (span {algebraMap _ BPlus xi}) BPlus

variable [Algebra R BPlus] [Algebra S BPlus] [IsScalarTower R S BPlus] in
deriving instance CommRing, Algebra R, IsScalarTower R S for @Bcris p _, @BdRPlus p _

attribute [instance 50] instAlgebraBcrisOfBPlus instAlgebraBdRPlusOfBPlus

instance [Algebra R Amax] : IsAdicComplete (span {(p : R)}) Amax :=
  isAdicComplete_over_base isAdicComplete

/-- The image of the period ring A in B^+ = A[1/p], as an A_inf-subalgebra. -/
def amaxImage := (toAlgHom Ainf Amax BPlus).range

/-- The element X = ξ/p of the period ring A: the image of the variable of A_inf[X]/(pX − ξ). -/
def Amax.X : Amax := .of _ _ (root _)

open Amax IsLocalization Away Function MulSemiringAction Quotient Set

instance isLocalizationAway_p_bPlus : Away (p : Amax) BPlus := isLocalization

instance : Away (mu : BPlus) Bcris := isLocalization

@[simp] lemma BPlus.isUnit_p : IsUnit (p : BPlus) := mod_cast algebraMap_isUnit (p : Amax)

/-- For a commutative Z_p-algebra R and a ring homomorphism f: R → O_C, the composite of f with
the inclusion O_C ⊂ C_p, as a Z_p-algebra homomorphism R → C_p. -/
abbrev OC.toPadicIntAlgHom [Algebra ℤ_[p] R] (f : R →+* OC) : R →ₐ[ℤ_[p]] ℂ_[p] :=
  ⟨𝓞_ℂ_[p].subtype.comp f,
  (congr($((ringHom_ext_of_approx (⟨_, by simp, mem_span_singleton.1 <| ·.appr_spec ·⟩) :
  f.comp _ = .codRestrict _ _ (by simpa using! (norm_algebraMap' ..).trans_le ·.2))) · |>.1))⟩

@[simp ←] lemma p_mul_X : p * X = xi := congr(.of _ _ $(sub_eq_zero.1 mk_self))

/-- The prime p is not a zero divisor in the period ring A, so A is p-torsion free. -/
lemma Amax.p_mem_nonZeroDivisors : ↑p ∈ Amax⁰ := mem_nonZeroDivisors_iff_left.2 fun _ ↦
  IsSMulRegular.right_eq_zero_of_smul
  (isSMulRegular_completion (.of_right_eq_zero_of_smul (Quot.ind fun _ h ↦
  ((prime_C_iff.2 Ainf.prime_p).left_dvd_or_dvd_right_of_dvd_mul (by simpa using mk_eq_zero.1 h)
  ).rec (by simpa using map_dvd constantCoeff ·) mk_eq_zero.2))) ∘ by simp

lemma Amax.exists_lift [IsAdicComplete (span {(p : R)}) R] (f : _ →+* R) x (h : f xi = p * x)
    : ∃ F : _ →+* R, (∀ a, F ↑a = f a) ∧ F X = x := ⟨(AdicCompletion.ofAlgEquiv
  (span {↑p})).symm.toRingHom.comp (adicMap (AdjoinRoot.lift f x (by aesop)) (by simp)), by
  and_intros <;> intros <;> erw [RingHom.comp_apply, adicMap_algebraMap] <;> simp⟩

lemma Amax.p_pow_dvd_of_mem_pow {n a} (h : a ∈ span {↑p, xi} ^ n) : (p : Amax) ^ n ∣ a
    := mem_span_singleton.1 ((span_singleton_pow ..).le (le_comap_pow _ _
  (pow_right_mono (by simp [span_insert, mul_mem_right]) n h)))

lemma Amax.exists_p_pow_dvd_sub_aeval a n : ∃ P : Ainf[X],
  p.cast ^ n ∣ a - aeval X P := by simpa [← aeval_eq,
  AdjoinRoot.mk_surjective.exists, ← aeval_algebraMap_apply] using! exists_approx a n

lemma Amax.exists_algebraMap_eq_p_pow_mul_sub y n : ∃ d a w, (a : Ainf) =
  p ^ d * (y - p ^ n * w : Amax) := (y.exists_p_pow_dvd_sub_aeval n).rec fun
  f ⟨c, h⟩ ↦ ⟨_, _, c, by simpa [p_mul_X, ← h] using! f.scaleRoots_eval₂_mul (algebraMap ..) X p⟩

attribute [local simp] IsUnit.pow smul_xi_mem_span NeZero.ne IsUnit.map

/-- Frobenius and `G_p` act on `A`. -/
instance actAmax : MulSemiringAction FrobGal Amax :=
  extendAction _ _ _ (fun _ ↦ (exists_lift ((algebraMap ..).comp (toRingHom ..)) _ (@pow_one .. ▸
  p_pow_dvd_of_mem_pow (by simp)).choose_spec).choose_spec.1) fun h ↦ ringHom_ext_of_approx
  (exists_algebraMap_eq_p_pow_mul_sub · · |>.rec fun _ ⟨a, _, e⟩ ↦ ⟨_, by simpa [e, pow_mem,
  mul_cancel_left_mem_nonZeroDivisors, p_mem_nonZeroDivisors] using (h a), _, sub_sub_self ..⟩)

instance : SMulDistribClass FrobGal Ainf Amax :=
  smulDistribClass_of_tower (by delta actAmax; generalize_proofs; tauto)

/-- Frobenius and `G_p` act on `B⁺`. -/
instance actBPlus : MulSemiringAction FrobGal BPlus := locAction _ (p : Amax) (by simp)

instance : SMulDistribClass FrobGal Amax BPlus := smulDistribClass_of_tower (lift_eq _)

instance : SMulDistribClass FrobGal Ainf BPlus := smulDistribClass_of_tower (lift_eq _)

instance : Algebra ℚ_[p] BPlus := (IsLocalization.lift (g := algebraMap ℤ_[p] _) fun y : _⁰ ↦
  PadicInt.unitCoeff_spec (coe_ne_zero y) ▸ by simp).toAlgebra

instance : IsScalarTower ℤ_[p] ℚ_[p] BPlus := of_algHom ⟨_, lift_eq _⟩

/-- The image of φ(ξ) in the period ring A equals p up to a unit of A. -/
lemma associated_p_frobEnd_xi : Associated (p : Amax) ↑(frobEnd xi) := by
  rw [← add_eq_of_eq_sub' associated_p_xi_sub_teichmuller.choose_spec, map_add, algebraMap.coe_add,
    frobEnd_teichmuller, (p_pow_dvd_of_mem_pow
    (pow_le_pow_right (Fact.out : 1 < p) (Ideal.pow_mem_pow ..))).choose_spec] <;>
    simp [sq, mul_assoc, ← mul_add, Witt.mem_span_pair_iff]
  exact ⟨(isUnit_of_dvd_sub (by simp) ⟨_, sub_eq_of_eq_add rfl⟩).unit, rfl⟩

/-- If a in A_inf divides μ, then for every m = (n, g) in ℕ × G_p the image of φ^n g(a) in B =
B^+[1/μ] is a unit. -/
lemma isUnit_smul_of_dvd_mu {a} (h : a ∣ mu) : IsUnit (↑(m • a) : Bcris) := @FrobGal.smul_def .. ▸
  isUnit_of_dvd (mu : BPlus) (Iterate.rec _ (map_dvd _ (by grw [← toRingHom_apply, h,
  toRingHom_apply, ← frobEnd_tau, smul_frobEnd, associated_smul_tau.dvd])) (fun _ ↦ (isUnit_of_dvd _
  associated_p_frobEnd_xi.dvd').dvd_mul_left.1 ∘ (by simpa [← xi_mul_tau] using! map_dvd frobEnd ·))
  _)

/-- Frobenius and `G_p` act on `B`. -/
instance actBcris : MulSemiringAction FrobGal Bcris := locAction _ (mu : BPlus)
  (by simp [← algebraMap_apply, isUnit_smul_of_dvd_mu])

instance [SMul FrobGal R] [Algebra R BPlus] [SMulDistribClass FrobGal R BPlus] :
    SMulDistribClass FrobGal R Bcris := smulDistribClass_of_tower (lift_eq _)

/-- The ring homomorphism from the period ring A to the integers of C_p that extends Fontaine's
θ on A_inf and sends X = ξ/p to 0. -/
def thetaAmax := (exists_lift theta 0 (by simp)).choose

/-- The ring homomorphism θ: B^+ = A[1/p] → C_p extending `thetaAmax`. -/
def thetaBPlus : BPlus →ₐ[ℚ_[p]] ℂ_[p] :=
  (liftAlgHom ↑p (f := OC.toPadicIntAlgHom thetaAmax) (by simp)).extendScalarsOfIsLocalization _ _⁰

/-- The map θ on the period ring A extends Fontaine's map: for a in A_inf, θ of the image of a
in A equals θ(a) in the ring of integers of C_p. -/
@[simp] lemma thetaAmax_algebraMap : thetaAmax a = theta a := by grind [thetaAmax]

/-- The map θ: B^+ → C_p extends θ on A: for a in the period ring A, θ of the image of a in B^+
equals θ(a), viewed in C_p. -/
@[simp] lemma thetaBPlus_algebraMap_Amax (a : Amax) : thetaBPlus a = (thetaAmax a).1 := lift_eq _ a

@[simp] lemma thetaBPlus_ainf : thetaBPlus a = (theta a).1 :=
  (thetaBPlus_algebraMap_Amax _).trans (by simp)

/-- The ring homomorphism θ: B^+ → C_p is surjective. -/
lemma thetaBPlus_surjective : Surjective thetaBPlus := (IsLocalization.lift_surjective_iff _).2
  (surj ↑p · |>.elim fun n ⟨a, _⟩ ↦ (theta_surjective a).rec fun b _ ↦
  ⟨⟨b, _, n, rfl⟩, by simp_all⟩)

namespace Amax

variable {p : _} [ThePrime p] {f : Ainf[X]}

/-- There is a ring homomorphism from A to (A_inf/(p, ξ))[X] with kernel pA that sends P(ξ/p) to
the reduction of P for every polynomial P over A_inf; so A/p = (A_inf/(p, ξ))[X]. -/
lemma exists_reduction_mod_p : ∃ F : _ →+* _,
  (∀ P, F (aeval X P) = P.map (Ideal.Quotient.mk (span {↑p, xi}))) ∧ ∀ y, ↑p ∣ y ↔
  F y = 0 := have := by simpa [image_pair] using congr($(map_quotient_self (span {↑p, xi})).map C)
  (@exists_lift _ _ _ _ (by simpa [*] using {}) (algebraMap ..) .X (by aesop)).imp fun F H ↦
    (⟨·, (exists_p_pow_dvd_sub_aeval · 1 |>.rec fun P hP ↦ ⟨by simp_all [dvd_def], fun _ ↦ by
    obtain ⟨a, b, rfl⟩ := mem_span_pair.1 (by simpa [*, ext_iff, eq_zero_iff_mem,
      ← mem_map_C_iff, image_pair] using map_dvd F hP)
    simp_all [mul_left_comm, dvd_sub_left, dvd_add]⟩)⟩)
    (by simp [*, aeval_def, eval₂, sum, Polynomial.map])

lemma p_pow_dvd_of_monic_mul (h : f.Monic) y m : p.cast ^ m ∣ aeval X f * y → p.cast ^ m ∣ y :=
  pow_dvd_of_map
  (by grind) p_mem_nonZeroDivisors (exists_reduction_mod_p.rec (by simp_all [(h.map _).isRegular]))

/-- Let ν in A_inf with ξ in the ideal (p, ν). For every n and every y in A there are a in A_inf
and z in A with p^n y = a + ν^n z. -/
lemma exists_p_pow_mul_eq_add {ν} (h : ∃ b, ν ∣ xi - p * b) n (y : Amax) : ∃ a z, p ^ n * y =
  (a : Ainf) + ν ^ n * z := h.rec fun b ⟨g, e⟩ ↦ n.rec ⟨0, by simp⟩ fun n ⟨a, z, k⟩ ↦
  (mem_range_of_approx (s := ⟨fun y ↦ ((@Fact.out (shiftDiff _ _).Surjective).prodMap (g :=
  shiftDiff _ _) Fact.out (_, _)).imp' ↿Function.prod fun _ ↦ congrArg ↿Function.prod⟩)
  ((algebraMap ..).toAddMonoidHom.coprod (.mulLeft _)) (map_natCast_smul _ Ainf ℤ p) id
  (by simpa using (exists_p_pow_dvd_sub_aeval · 1 |>.rec fun P ⟨c, k⟩ ↦ ⟨_, _, c, by
  simpa using congr(aeval X $((P.modByMonic_add_div (.X - C b)).symm) + $k)⟩)) z).elim fun c l ↦ ⟨p
  * (a + ν ^ n * c.1), g * c.2, by replace e := congr(($e : Amax)); simp_all; grind⟩

/-- If the image in A of an element a of A_inf is divisible by p^m, then a lies in the ideal (p,
ξ)^m of A_inf. -/
lemma mem_span_pow_of_p_pow_dvd {a : Ainf} {m} (h : (p : Amax) ^ m ∣ a) :
  a ∈ span {↑p, xi} ^ m := by
  induction m generalizing a; simp
  choose c k using theta_surjective.exists.1 (map_dvd thetaAmax h)
  cases (@theta_eq_zero_iff_xi_dvd p _ (a - p ^ ‹ℕ›.succ * c)).1 (by aesop)
  simp_all [pow_succ', mul_assoc, dvd_add_left, sub_eq_iff_eq_add,
    dvd_cancel_left_mem_nonZeroDivisors p_mem_nonZeroDivisors]
  aesop (add 1% Ideal.mul_mem_mul, simp (p_pow_dvd_of_monic_mul monic_X))
