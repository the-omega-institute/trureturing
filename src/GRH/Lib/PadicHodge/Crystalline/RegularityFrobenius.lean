import GRH.Lib.PadicHodge.WachKisin.KummerChart
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Potentially crystalline representations, Hodge–Tate weights and the Weil–Deligne
Frobenius. The file uses abstract modules over any p-adic coefficient ring, takes Colmez's B_max as
period ring, and defines crystalline by the condition that the invariants span. Polynomials killing
one linear Frobenius replace the Weil–Deligne representation. Source: J.-M. Fontaine,
Représentations p-adiques semi-stables (Exp. III §1, §5) and Représentations l-adiques
potentiellement semi-stables (Exp. VIII 2.3), Astérisque 223 (1994); O. Brinon, B. Conrad, CMI
Summer School notes on p-adic Hodge theory (2009), 2.3.1, 5.2.1, 6.3, 9.1–9.3.

This file: Admissibility under subobjects, tensors, duals; the linear Weil–Deligne Frobenius and
killing polynomials. -/


open TensorProduct Filter Classical Submodule Finsupp Module LinearMap Function Polynomial Lift Free
  Bcris Multiplicative IsPrincipal Fint Multiset
attribute [-simp] Set.forall_neg_mem _root_.map_eq_zero map_smul_of_tower smul_assoc
attribute [local simp] isWeilPair_zero_iff tensorAction_smul
variable {p} [ThePrime p] {Γ R'} [Group Γ] [CommRing R'] [Algebra ℤ_[p] R'] [𝒥 : OverGp Γ p] {F} (hF
  : nearOne Γ ≤ F) {s t m k R T T' T''} [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup T'] [Module R' T'] [Module ℤ_[p] T']
  [IsScalarTower ℤ_[p] R' T'] {ρ σ : Representation R Γ T} {ρ' : Representation R' Γ _} {ι κ :
  Type*} (h : IsPotCrys ρ) (hs : IsWeilPair (𝒥.toGp s) m) {b : Bcris} [Finite κ] {S : κ → _} [∀ i,
  AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, Module ℤ_[p] (S i)] [∀ i, IsScalarTower ℤ_[p] R (S
  i)] {τ : ∀ _, Representation R Γ _} {P} (hA : ∀ i, IsAdmissible (τ i) F) (f : ∀ i, T' →ₗ[ℤ_[p]] S
  i) (hf : ∀ i, ∀ᶠ g in F, ∀ x, f i (ρ' g x) = τ i g (f i x)) (hi : ∀ x, (∀ i, f i x = 0) → x = 0)

lemma eventually_tensorAction_eq {x : ι → _} (hx : ∀ i, x i ∈ fixedPeriods ρ Bcris F) a : ∀ᶠ g in F,
  tensorAction _ (toGp
  g) (ρ g) (linearCombination Bcris x a) = linearCombination _ x (toGp g • a) := a.induction_linear
  (by simp) (fun _ _ ↦ (·.mp <| ·.mp (by aesop))) fun i _ ↦ (hx i).mp (by aesop)

@[simp] lemma coefEnd_tmul a b x : coefEnd R T a (b ⊗ₜ x) = b ⊗ₜ (a • x) := rfl

/-- Let K be algebraically closed of characteristic 0 and φ: K[X] → A a ring homomorphism with
φ(X)^n = 1 for some n > 0. If φ(Q) = 0, then φ(P) = 0 for every P vanishing at all roots of
Q. -/
lemma map_eq_zero_of_roots {K A} [Field K] [IsAlgClosed K] [CharZero K] [Ring A] (φ : K[X] →+* A) {P
  Q} : (∃ n > 0, φ X ^ n = 1) → φ Q = 0 → (∀ x, Q.IsRoot x → P.IsRoot x) → φ P = 0 := fun ⟨n, k⟩ ↦
  by grind [(X_pow_sub_one_separable_iff.2 (mod_cast k.1.ne')).of_dvd ((mem_iff_generator_dvd
  (RingHom.ker φ)).1 (by aesop)), mem_iff_generator_dvd, =_ RingHom.mem_ker, mem_roots', IsRoot.dvd,
  Separable.ne_zero, nodup_roots, le_iff_subset, subset_iff, = IsAlgClosed.dvd_iff_roots_le_roots]

lemma IsWeilPair.inv : IsWeilPair (toGp s) 0 → IsWeilPair (toGp s⁻¹) 0 := by simp

include hi in
open AlgebraTensorModule in
lemma exists_retraction : ∃ Ψ : _ →ₗ[Bcris] _, LeftInverse Ψ fun x i ↦ (f i).baseChange Bcris x :=
  ⟨liftBaseChange _ (curry (lTensor ℚ_[p] Bcris (pi f)).leftInverse 1) ∘ₗ piRightInv .., fun x ↦ by
  induction x <;> simp_all [← Pi.add_def, ← Pi.zero_def]
  erw [leftInverse_apply_of_inj (ker_eq_bot.2 (Flat.lTensor_preserves_injective_linearMap _
    (.of_ker _ (hi · ∘ congrFun)))) (1 ⊗ₜ _), ← tmul_eq_smul_one_tmul]⟩

section

include hF

/-- Fontaine's regularity: let j have open image and every set of F contain the preimage of a
neighbourhood of 1. If b ≠ 0 in B, w ∈ B^(ι) and b·gw = (gb)·w along F, then w = b·a with a
∈ B^(ι) fixed along F. -/
lemma fontaine_regularity (w : ι →₀ Bcris) (n : b ≠ 0) (h : ∀ᶠ g in F, b • toGp g • w = (toGp g •
  b) • w) : ∃ a, w = b • a ∧ ∀ᶠ g in F, toGp g • a = a := ((range_mapRange _ (mul_zero b)).ge
  fun i ↦ .imp (by tauto) (let ⟨_, m, _,
    e⟩ := exists_witt_ratio n (nhds_one_le_map_nearOne Γ (hF (h.mono fun _ k ↦ congr($k i))))
  ((BPlus.isUnit_p.pow m).map (algebraMap ..)).dvd_mul_left.1 (by simp [e]))).imp
  (by rintro a rfl; simp_all [Finsupp.ext_iff, mul_left_comm b, smul_eq_zero_iff_eq])

/-- Elimination. Let j have open image, F be coarser than 'near 1', and W ⊂ B^(ι) a saturated
submodule, each v in W having j(g)v in W for F-almost all g. Then the vectors of W fixed by
F-almost all g span W. -/
lemma le_of_fixed_mem_of_saturated {W W' : Submodule Bcris (ι →₀ Bcris)} (hs : ∀ b ≠ (0 : Bcris),
  ∀ w, b • w ∈ W → w ∈ W) (hW : ∀ v ∈ W, ∀ᶠ g in F, toGp g • v ∈ W) (H : ∀ w ∈ W, (∀ᶠ g in F,
  toGp g • w = w) → w ∈ W') : W ≤ W' := le_of_echelon 1 fun v hv n h ↦ (ne_iff.1 n).rec fun k n ↦
  (fontaine_regularity hF v n ((hW v hv).mono fun _ ↦ (h _ · (by aesop) k))).imp
  (by simp; grind [Finsupp.smul_apply, smul_eq_mul, left_eq_mul₀, mul_eq_zero])

/-- Let j have open image and every set of F contain the preimage of a neighbourhood of 1. If
the elements of B⊗T fixed by F-almost all g span B⊗T over B = `Bcris`, then B⊗T has a
B-basis of such elements. -/
lemma IsAdmissible.exists_basis (h : IsAdmissible ρ F) : ∃ s : Set (fixedPeriods ρ Bcris F), ∃ v :
  Basis s Bcris _, ∀ i, v i ∈ fixedPeriods ρ Bcris F :=
  (exists_maximal_linearIndepOn _ (·.1)).imp fun s ⟨hs, hm⟩ ↦ ⟨.mk
  (id hs) (h ▸ span_le.2 fun y hy ↦ byCases (subset_span ⟨⟨⟨_, hy⟩, ·⟩, rfl⟩) (by
  rw [Set.image_eq_range, ← range_linearCombination] at *
  exact (hm _ · |>.rec fun b ⟨hb, w, o⟩ ↦
    (fontaine_regularity hF w hb ((eventually_tensorAction_eq (·.1.2) w).mp
    (hy.mono fun g k l ↦ hs (by simp [*, smul_comm b, ← l])))).imp (by aesop)))), by simp⟩

include hA

lemma IsAdmissible.of_retraction (Φ : ∀ i, _ →ₗ[Bcris] Bcris ⊗ S i) (H : ∀ i, ∀ᶠ g in F, ∀ x,
  Φ i (tensorAction Bcris (toGp g) (ρ' g) x) = tensorAction _ (toGp g) (τ i g) (Φ i x)) (Ψ :
  _ →ₗ[Bcris] _) (e : LeftInverse Ψ (pi Φ)) : IsAdmissible ρ' F := by
  choose s v hv using (hA · |>.exists_basis hF)
  let Θ := (Pi.basis v).1.1 ∘ₗ pi Φ; have I : Injective Θ := by simp [Θ, e.injective]
  have E x : ∀ᶠ g in F, Θ (tensorAction _ (toGp g) (ρ' g) x) = toGp g • Θ x := .mono (.all fun i ↦
    (H i).and (eventually_tensorAction_eq (hv i) ((v i).1 (Φ i x)))) (by aesop)
  exact top_unique ((gciMapComap I).l_le_l_iff.1 (le_of_fixed_mem_of_saturated hF
    (by simp_all [Θ, range_comp, range_eq_ker_of_leftInverse e]) (by simp; peel E; bound)
    fun _ ⟨y, h⟩ k ↦ ⟨y, subset_span ((E y).mp (k.mono (by lia))), h.2⟩))

include hf hi

/-- Let every set of the filter F contain the j-preimage of a neighbourhood of 1. If finitely
many jointly injective Z_p-linear f_i: T' → S_i are equivariant along F, and elements fixed
along F span each B⊗S_i, they span B⊗T'. -/
lemma IsAdmissible.of_jointly_injective : IsAdmissible ρ' F := (exists_retraction f hi).rec
  (.of_retraction hF hA _ (hf · |>.mono fun _ ↦ (tensorAction_periodTensorMap · _ · |>.symm)))

end

section

include hs

/-- Let j have open image and let (j(s), m) be a Weil pair. If b in B is fixed by j(g) for all g
near 1, then φ^m j(s) fixes b. -/
lemma IsWeilPair.smul_eq_of_fixed_nearOne (h : ∀ᶠ g in nearOne Γ, toGp g • b = b) :
  (ofAdd m, toGp s) • b = b := by
  obtain ⟨f, n, w, e⟩ := exists_witt_ratio one_ne_zero (nhds_one_le_map_nearOne Γ (by simpa))
  simpa [← smul_algebraMap_eq_algebraMap_smul, ← by simpa using e, (NeZero.of_faithfulSMul ℚ_[p]
    ..).1] using congrArg (algebraMap _ Bcris) ((w.exists_smul_algebraMap_eq _).rec fun _ k ↦
    (wittFq_map_residue_injective (k ▸ toWittResidue_smul_of_isFrob hs _ :) ▸ k :))

include h

/-- For j with open image, T potentially crystalline and (j(s), m) a Weil pair, the operator
β_{s,m} agrees with φ^m j(s) ⊗ ρ(s) on every element d of B⊗T fixed near 1. -/
@[local simp] lemma linearFrob_apply {d} : d ∈ Dpcris ρ → linearFrob ρ s m d =
  tensorAction _ (ofAdd m, toGp s) (ρ s) d := let ⟨_, v, hv⟩ := h.exists_basis le_rfl
  @epsilon_spec (End ..) (∀ d ∈ _, · d = _) ⟨v.constr ℕ _, (reindex_equiv v.1.symm).1.2 fun c a ↦ by
     simp [(hs.smul_eq_of_fixed_nearOne (b := c ·) (.mp a ((eventually_tensorAction_eq hv c).mp
       (by simp_all [v.ext_elem_iff])))), Finsupp.sum, linearCombination]
     rfl⟩ d

/-- Multiplicativity of the linear Frobenius: for j with open image, T potentially crystalline,
and Weil pairs (j(s), m) and (j(t), k), one has β_{st, m+k} = β_{s,m} β_{t,k}. -/
lemma linearFrob_mul (ht : IsWeilPair (toGp t) k) : linearFrob ρ (s * t) (m + k) =
  linearFrob ρ s m * linearFrob ρ t k := ext_on h fun d hd ↦ .trans (by simp_all [↓hs.mul,
  tensorAction_tensorAction]) (linearFrob_apply h hs (linearFrob_apply h
  ht hd ▸ ((tendsto_comap_iff.2 (by convert (tendsto_comap.const_mul _).mul_const (toGp t) <;>
  aesop) : Tendsto (t⁻¹ * · * t) (nearOne Γ) _).eventually hd).mono fun g e ↦ .trans (by
    repeat erw [tensorAction_tensorAction (M := FrobGal)]; simp [← map_mul, mul_assoc])
  (congrArg _ e))).symm

lemma linearFrob_pow n : linearFrob ρ (s ^ n) (n * m) = linearFrob ρ s m ^ n :=
  n.rec (ext_on h fun _ hd ↦ by simpa [*] using! mem_of_mem_nhds (mem_comap'.1 hd) toGp.map_one)
  (by simp_all [pow_add, add_mul, linearFrob_mul, ↓hs.pow])

/-- Let T, T' be potentially crystalline, (j(s), m) a Weil pair, f: T → T' Z_p-linear and
equivariant for s and for all g near 1. Then 1⊗f: B⊗T → B⊗T' intertwines the operators
β_{s,m} of T and T'. -/
lemma baseChange_linearFrob (h' : IsPotCrys ρ') (f : T →ₗ[_] _) (hf : ∀ᶠ g in nearOne Γ ⊔ pure s,
  ∀ x, f (ρ g x) = ρ' g (f x)) x : f.baseChange _ (linearFrob ρ s m x) = linearFrob ρ' s m
  (f.baseChange _ x) := by induction eq_top_iff'.1 h x using span_induction <;> simp_all
  [fixedPeriods.map hf.1, tensorAction_periodTensorMap hf.2, baseChange_eq_periodTensorMap]

lemma commute_coefEnd_linearFrob a : Commute (coefEnd R T a) (linearFrob ρ s m) :=
  ext (baseChange_linearFrob h hs h _ (by simp))

/-- For j with open image, ρ potentially crystalline, (j(s), m) a Weil pair, d a natural number
and σ the twist of ρ by χ^(−d), the operator β_{s,m} of σ equals p^(md) times that of ρ. -/
lemma linearFrob_twist_cyclotomicGp (d : ℕ) (e : ∀ g x, σ g x = (χ g ^ (-d : ℤ)).1 • ρ g x) :
  linearFrob σ s m = (p : Bcris) ^ (m * d) • linearFrob ρ s m :=
  ext_on h fun y a ↦ let ⟨_, _, l, k⟩ := exists_tate_twist_unit _ e
  by simpa [*, mul_smul, zpow_mul, pow_mul] using
    (linearFrob_apply (h.tate_twist _ e) hs (a.out.mono fun g a ↦ k 0 g y ▸ by simpa)).trans (k ..)

end

include hs hf hi in
/-- Let T' have jointly injective φ-semilinear maps, equivariant near 1 and at s, to finitely
many potentially crystalline S_i on which P = φ(Q) kills the Weil pair (s,m), j having open
image. Then T' is potentially crystalline and Q kills (s,m) on T'. -/
lemma IsKilledBy.of_jointly_injective (k : nearOne Γ ⊔ pure s ≤ F) (h : ∀ i, IsKilledBy (τ i) s m P)
    {φ Q} (e : .map φ Q = P) (hφ : ∀ i a x, f i (a • x) = φ a • f i x) : IsKilledBy ρ' s m
  Q := have a := IsAdmissible.of_jointly_injective le_rfl (h · |>.1) f (hf · |> k |>.1) hi
  ⟨a, ext fun x ↦ (exists_retraction f hi).choose_spec.injective (funext fun i ↦ .trans (by
      clear e; induction Q using recOnHorner generalizing x <;>
        simp [*, baseChange_linearFrob a hs (h i).1 _ (k (hf i))]
      induction x <;> simp [*]) (congr($((e ▸ h i :).2) (baseChange _ (f i) x)).trans (by simp)))⟩

/-- For j with open image, T crystalline and j(s) in inertia, the operator β_{s,0} on B⊗T is the
identity. -/
lemma IsCrystalline.linearFrob_eq_one (h : IsCrystalline ρ) (hs : IsWeilPair (toGp s) 0) :
  linearFrob ρ s 0 = 1 :=
  ext_on h fun _ hd ↦ linearFrob_apply h.isPotCrys hs ((nearOne Γ).univ_mem' hd) ▸ hd s

variable [AddCommGroup T''] [Module R T''] [Module ℤ_[p] T''] [IsScalarTower ℤ_[p] R T''] (c : ℤ)
  {σ : Representation R Γ T''} (v : IsPotCrys σ)
  (B : (_ →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] T' : Type)) (e : ∀ g x y, B (σ g x) (ρ g y) = ρ' g (B x y))

/-- For T finite free over R and potentially crystalline, β_{g,0} is the identity for all g such
that j(g) is close enough to 1 and lies in inertia. -/
lemma IsPotCrys.eventually_linearFrob_eq_one [Module.Finite R T] [Free.{0} R T]
    (h : IsPotCrys ρ) : ∀ᶠ g in nearOne Γ,
  IsWeilPair (toGp g) 0 → linearFrob ρ g 0 = 1 := by
  choose n a d hd using (mem_span_set'.1 <| h.ge (x := 1 ⊗ₜ chooseBasis R T ·) ⟨⟩)
  filter_upwards [Eventually.all fun l ↦ .all (d l · |>.2)] with g k s
  ext t; rw [← (chooseBasis R T).sum_repr t]
  simp [↓map_sum, ← coefEnd_tmul, ← End.mul_apply, ← (commute_coefEnd_linearFrob h s _).eq]
  simp [← hd, linearFrob_apply h s _ ▸ k _ _]

include e

lemma baseChangePairing_mem_fixedPeriods {x y} : x ∈ fixedPeriods σ _ F → y ∈ fixedPeriods ρ _ F →
  baseChangePairing B x y ∈ fixedPeriods ρ' Bcris F := (·.mp <| ·.mono fun g k h ↦
  (baseChangePairing_map _ (e g) ..).symm.trans congr(baseChangePairing B $h $k))

/-- Let the values of a Γ-equivariant Z_p-bilinear map T'' × T → T' span T' over Z_p. If T'' and T
are spanned, after tensoring with the period ring, by elements fixed along F, so is T'. -/
lemma IsAdmissible.of_bilinear (h : IsAdmissible σ F) (k : IsAdmissible ρ F) (H : Surjective
  (lift B)) : IsAdmissible ρ' F := isAdmissible_of_one_tmul_mem_span (H.forall.2 fun z ↦ by
  induction z <;> simp_all [tmul_add, add_mem]
  simpa [baseChangePairing] using BilinMap.apply_apply_mem_of_mem_span _ _ _ _ (fun _ a _ b ↦
    subset_span (baseChangePairing_mem_fixedPeriods B e a b)) (1 ⊗ₜ _) (1 ⊗ₜ _) (h.ge ⟨⟩) (k.ge ⟨⟩))

include h hs v in
/-- `linearFrob` is compatible with tensor products. -/
lemma linearFrob_baseChangePairing (w : IsPotCrys ρ') : (baseChangePairing B).compl₁₂ (linearFrob σ
  s m) (linearFrob ρ s m) = (baseChangePairing B).compr₂ (linearFrob ρ' s m) := ext_on v fun _ _ ↦
  ext_on h fun _ _ ↦ by simp_all [linearFrob_apply,
  baseChangePairing_mem_fixedPeriods B e]; exact baseChangePairing_map _ (e s) ..

omit e
include hF

/-- Let F be coarser than 'near 1', T finite free over R with `IsAdmissible` for F, and T'' ≅
Hom_R(T, R(c)) equivariantly. Then T'' has `IsAdmissible` for F, and on inertia what kills
(s, 0) on T kills (s⁻¹, 0) on T''.

Known result: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne
Frobenius. -/
lemma IsAdmissible.of_pairing [Module.Finite R T] [Free.{0} R T]
    (w : IsAdmissible ρ F) (b : T'' ≃ₗ[R] T →ₗ[R] R) (H : ∀ g x y,
  b (σ g x) (ρ g y) = (χ g ^ c).1 • b x y) : IsAdmissible σ F ∧ ∀ s Q, IsWeilPair (toGp s) 0 →
  IsKilledBy ρ s 0 Q → IsKilledBy σ s⁻¹ 0 Q := by
  let B := b.restrictScalars₁₂ ℤ_[p] ℤ_[p]
  have A {F : Filter Γ} : IsAdmissible (charRep R (χ ^ c)) F :=
    isAdmissible_of_cyclotomicGp_zpow c (by tauto)
  let ⟨Ψ, r⟩ := exists_retraction (B.flip ∘ chooseBasis R T) fun _ ↦
    (b.map_eq_zero_iff.1 <| Basis.ext _ ·)
  have q a y x : (B.flip y).baseChange _ (coefEnd R _ a x) = baseChangePairing B x (1 ⊗ₜ (a •
    y)) := by induction x <;> simp_all [B, baseChangePairing, smul_tmul']
  choose n a d hd using (mem_span_set'.1 <| w.ge (x := 1 ⊗ₜ chooseBasis R T ·) ⟨⟩)
  have v := of_retraction hF (fun _ ↦ A) ((baseChangePairing B).flip <| d _ <| Sigma.snd ·) (d _ ·.2
    |>.2.mono fun g h x ↦ (congrArg _ h).symm.trans (baseChangePairing_map _ (H g) ..)) (Ψ ∘ₗ pi
    fun l ↦ ∑ k, a l k • proj ⟨l, k⟩) (by simpa [← hd, LinearMap.pi, by simpa using q 1] using! r)
  use v, fun s Q hs ⟨P, K⟩ ↦ (fun v ↦ ⟨v, ext fun x ↦ r.injective (funext ?_)⟩) (v.mono hF)
  obtain _ := linearFrob_pow v hs 0, fun s (h : IsWeilPair (toGp s) 0) ↦
    congr($(linearFrob_baseChangePairing P h v B ‹_› A) ∘ₗ linearFrob σ s⁻¹ 0)
  simp_all [DFunLike.ext_iff, ← End.mul_apply, ← linearFrob_mul, IsCrystalline.linearFrob_eq_one A]
  simpa [eval₂_eq_sum_range, ← linearFrob_pow, pow_mem, *,
    (commute_coefEnd_linearFrob P ..).eq] using fun _ ↦ congr(baseChangePairing B x $(K (1 ⊗ₜ _)))
