/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reconstruct the weighted signed ribbon boundary state sum from physical quotient-code moments of its intrinsic signed pairing. -/

import D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset LinearMap Submodule
open scoped BigOperators Classical
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
variable {n : ℕ} {I E : Type*} [Fintype I] [Fintype E] [DecidableEq E]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def signedEntry (a b : I → D n) (t : I → Bool) (i j : I) : K :=
    (if interlaces a b i j then 1 else 0) + (if t i ∧ j = i then 1 else 0)

private theorem signedMap_apply_entry (a b : I → D n) (t : I → Bool) (z : I → K) (i : I) :
    (interlacementMap a b + twistDiagonal t) z i = ∑ j, z j * signedEntry a b t i j := by
  classical
  have ht : (∑ j : I, if t i ∧ j = i then z j else 0) = if t i then z i else 0 := by
    cases t i <;> simp
  rw [LinearMap.add_apply,Pi.add_apply,interlacementMap_apply,twistDiagonal_apply,← ht, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold signedEntry
  rw [mul_add]
  by_cases h : interlaces a b i j <;> by_cases k : t i ∧ j=i <;> simp [h,k]

omit [FiniteDimensional K V] in
private theorem signed_image_rank (a b : I → D n) (t : I → Bool)
    (ell : I → V) (B : LinearMap.BilinForm K V)
    (hp : ∀ i j, B (ell j) (ell i) = signedEntry a b t i j) :
    let U := (Fintype.linearCombination K ell).range
    Module.finrank K (interlacementMap a b + twistDiagonal t).range =
      Module.finrank K (B.restrict U).range := by
  classical
  let A := Fintype.linearCombination K ell
  let U := A.range
  let L := A.rangeRestrict
  let C := (B.restrict U).compl₁₂ L L
  have hL : Function.Surjective L := LinearMap.range_eq_top.mp A.range_rangeRestrict
  have hC := pullback_pairing_rank L hL (B.restrict U)
  have hc (z : I→K) (i : I) : C z (Pi.single i 1) =
      (interlacementMap a b + twistDiagonal t) z i := by
    rw [signedMap_apply_entry]
    change B (A z) (A (Pi.single i 1)) = _
    rw [show A (Pi.single i 1)=ell i by simp [A,Fintype.linearCombination_apply_single]]
    rw [show A z=∑ j, z j • ell j by exact Fintype.linearCombination_apply K ell z,
      map_sum]
    simp only [LinearMap.sum_apply,map_smulₛₗ,RingHom.id_apply,LinearMap.smul_apply,smul_eq_mul,hp]
  have hk : C.ker = (interlacementMap a b + twistDiagonal t).ker := by
    ext z
    change C z=0 ↔ (interlacementMap a b + twistDiagonal t) z=0
    constructor
    · intro hz
      funext i
      rw [← hc, hz]
      rfl
    · intro hz
      apply (Pi.basisFun K I).ext
      intro i
      rw [Pi.basisFun_apply,hc,hz]
      rfl
  have h₁ := LinearMap.finrank_range_add_finrank_ker C
  have h₂ := LinearMap.finrank_range_add_finrank_ker (interlacementMap a b + twistDiagonal t)
  rw [hk] at h₁
  change Module.finrank K C.range = _ at hC
  change _ = Module.finrank K (B.restrict U).range
  exact (Nat.add_right_cancel (h₂.trans h₁.symm)).trans hC

omit [Fintype E] [DecidableEq E] [FiniteDimensional K V] in
private theorem span_of_selected_labels (ell : E → V) (S : Finset E) :
    (Fintype.linearCombination K (fun i : S => ell i)).range = columns (F:=K) ell S := by
  rw [Fintype.range_linearCombination, columns]
  congr 1
  ext y
  change (∃ i : S, ell i = y) ↔ ∃ i, i ∈ (S : Set E) ∧ ell i = y
  exact ⟨fun ⟨i,hi⟩ => ⟨i,i.prop,hi⟩, fun ⟨i,hi,he⟩ => ⟨⟨i,hi⟩,he⟩⟩

noncomputable def signedCoeff [Fintype (Submodule K V)]
    [∀ L : Submodule K V, Fintype (Module.Dual K (V ⧸ L))]
    (ell : E → V) (coeff : Submodule K V → ℝ) (S : Finset E) : ℝ :=
  ∑ L : Submodule K V, coeff L * readMoment (F:=K) (L.mkQ ∘ ell)
    ((Module.finrank K V : ℝ)+1) S

omit [FiniteDimensional K V] in
private theorem restriction_euler_from_labels
    (a b : E → D n) (t : E → Bool) (ell : E → V) (B : LinearMap.BilinForm K V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val)
    (hPair : ∀ i j, B (ell j) (ell i) = signedEntry a b t i j) (S : Finset E) :
    signedBouquetCircleCount a b t S +
      Module.finrank K ((B.restrict (columns (F:=K) ell S)).range) = 1 + S.card := by
  classical
  have hr : Module.finrank K ((B.restrict (columns (F:=K) ell S)).range) =
      Module.finrank K (interlacementMap (fun i : S => a i) (fun i : S => b i) +
        twistDiagonal (fun i : S => t i)).range := by
    have hx := signed_image_rank (fun i : S => a i) (fun i : S => b i)
      (fun i : S => t i) (fun i : S => ell i) B (fun i j => by
        have he : interlaces (fun i : S => a i) (fun i : S => b i) i j ↔ interlaces a b i.val j.val := by
          simp only [interlaces]
          rw [Subtype.coe_ne_coe]
        have hdg : (t i.val ∧ j = i) ↔ (t i.val ∧ j.val = i.val) :=
          ⟨fun h => ⟨h.1,congrArg Subtype.val h.2⟩, fun h => ⟨h.1,Subtype.ext h.2⟩⟩
        apply (hPair i.val j.val).trans
        unfold signedEntry
        rw [he]
        by_cases hh : t i.val ∧ j.val = i.val
        · rw [ite_eq_left hh, ite_eq_left (hdg.mpr hh)]
        · rw [ite_eq_right hh, ite_eq_right (fun hk => hh (hdg.mp hk))])
    dsimp only at hx
    rw [span_of_selected_labels] at hx
    exact hx.symm
  have hc := signed_flag_boundary_plus_rank (fun i : S => a i) (fun i : S => b i)
    (fun i : S => t i) (ha.comp Subtype.val_injective) (hb.comp Subtype.val_injective)
    (fun i j => hd i j) (fun i => hord i)
  rw [← hr, Fintype.card_coe] at hc
  change signedBouquetCircleCount a b t S +
    Module.finrank K ((B.restrict (columns (F:=K) ell S)).range) = 1 + S.card at hc
  exact hc

set_option maxHeartbeats 45000 in
private theorem literal_signed_pairing_walsh [Fintype V] [Fintype (Submodule K V)]
    [∀ L : Submodule K V, Fintype (Module.Dual K (V ⧸ L))]
    (a b : E → D n) (t : E → Bool) (ell : E → V) (B : LinearMap.BilinForm K V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val)
    (hPair : ∀ i j, B (ell j) (ell i) = signedEntry a b t i j)
    (u v : E → ℝ) (d : ℝ) (hdLoop : d ≠ 0) :
    ∃ α : Submodule K V → ℝ,
    d*(∑ T : Finset E, inverse (signedCoeff ell α) T*
      (∏ e : E, (v e+(d*u e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, u e)*(∏ e ∈ Sᶜ, v e))*d^(signedBouquetCircleCount a b t S) := by
  classical
  let q (W : Submodule K V) := (d⁻¹) ^ Module.finrank K (B.restrict W).range
  obtain ⟨α,hα⟩ := physical_lattice_reconstruction ell q
  refine ⟨α,?_⟩
  rw [weighted_walsh, Finset.mul_sum]
  apply sum_congr rfl
  intro S _
  have hc := restriction_euler_from_labels a b t ell B ha hb hd hord hPair S
  have hpow : d * d^S.card * q (columns (F:=K) ell S) = d^(signedBouquetCircleCount a b t S) := by
    have haPow : d * d^S.card = d^(1 + S.card) := by rw [pow_add,pow_one]
    rw [haPow, ←hc]
    dsimp only [q]
    rw [pow_add,inv_pow, mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hdLoop),mul_one]
  have hs : signedCoeff ell α S = q (columns (F:=K) ell S) := hα S
  rw [hs, Finset.prod_mul_distrib, Finset.prod_const]
  calc
    _ = ((∏ e ∈ S, u e)*(∏ e ∈ Sᶜ, v e)) * (d * d^S.card * q (columns (F:=K) ell S)) := by ac_rfl
    _ = _ := by rw [hpow]

#print axioms signed_image_rank
#print axioms literal_signed_pairing_walsh
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

open Finset LinearMap Submodule
open scoped BigOperators Classical
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def signedBilin (a b : E → D n) (t : E → Bool) :
    LinearMap.BilinForm K (E → K) :=
  LinearMap.mk₂ K
    (fun x y => ∑ i, y i * (interlacementMap a b + twistDiagonal t) x i)
    (by intro x x' y; simp [map_add, mul_add, sum_add_distrib])
    (by intro c x y; simp [map_smul, mul_left_comm, Finset.mul_sum])
    (by intro x y y'; simp [add_mul, sum_add_distrib])
    (by intro c x y; simp [mul_assoc, Finset.mul_sum])

private theorem signedBilin_port (a b : E → D n) (t : E → Bool) (i j : E) :
    signedBilin a b t (Pi.single j 1) (Pi.single i 1) = signedEntry a b t i j := by
  classical
  change (∑ x, (Pi.single i (1:K) : E → K) x * ((interlacementMap a b + twistDiagonal t)
    (Pi.single j 1)) x) = _
  have h (y : E → K) (i : E) : (∑ j, (Pi.single i (1:K) : E → K) j * y j) = y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [h, signedMap_apply_entry]
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    simp [Pi.single_eq_of_ne hx]
  · simp

private theorem interlaces_swap (a b : E → D n)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val) (i j : E) :
    interlaces a b i j ↔ interlaces a b j i := by
  classical
  by_cases h : i = j
  · subst j; rfl
  have hAA : (a i).val ≠ (a j).val := fun h' => h (ha (Fin.ext h'))
  have hBB : (b i).val ≠ (b j).val := fun h' => h (hb (Fin.ext h'))
  have hAB : (a i).val ≠ (b j).val := fun h' => hd _ _ (Fin.ext h')
  have hBA : (a j).val ≠ (b i).val := fun h' => hd _ _ (Fin.ext h')
  have hi := hord i
  have hj := hord j
  simp only [interlaces, between]
  constructor
  · rintro ⟨_,hv⟩
    refine ⟨Ne.symm h, ?_⟩
    omega
  · rintro ⟨_,hv⟩
    refine ⟨h, ?_⟩
    omega

private theorem signedBilin_symmetric (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val) :
    (signedBilin a b t).flip = signedBilin a b t := by
  classical
  apply (Pi.basisFun K E).ext
  intro i
  apply (Pi.basisFun K E).ext
  intro j
  simp only [Pi.basisFun_apply]
  change signedBilin a b t (Pi.single j 1) (Pi.single i 1) =
    signedBilin a b t (Pi.single i 1) (Pi.single j 1)
  simp only [signedBilin_port, signedEntry]
  rw [interlaces_swap a b ha hb hd hord i j]
  by_cases h : i=j
  · subst j; rfl
  · simp [h,Ne.symm h]

section Compression
variable {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
  (B : LinearMap.BilinForm F X)

noncomputable def radicalFirst : (X ⧸ B.ker) →ₗ[F] Module.Dual F X :=
  B.ker.liftQ B le_rfl

private theorem radicalFirst_apply (x y : X) : radicalFirst B (B.ker.mkQ x) y = B x y := rfl

private theorem radical_second (hB : B.flip=B) : B.ker ≤ (radicalFirst B).flip.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro h
  obtain ⟨y,rfl⟩ := B.ker.mkQ_surjective h
  change radicalFirst B (B.ker.mkQ y) x = 0
  rw [radicalFirst_apply]
  have hxx := congrArg (fun M : LinearMap.BilinForm F X => M x y) hB
  change B y x = B x y at hxx
  rw [hxx, LinearMap.mem_ker.mp hx]
  rfl

noncomputable def radicalForm (hB : B.flip=B) : LinearMap.BilinForm F (X ⧸ B.ker) :=
  (B.ker.liftQ (radicalFirst B).flip (radical_second B hB)).flip

private theorem radicalForm_apply (hB : B.flip=B) (x y : X) :
    radicalForm B hB (B.ker.mkQ x) (B.ker.mkQ y) = B x y := rfl
end Compression

abbrev SignedLabelSpace (a b : E → D n) (t : E → Bool) :=
  (E→K) ⧸ (signedBilin a b t).ker

noncomputable def intrinsicLabel (a b : E → D n) (t : E → Bool) (i : E) :
    SignedLabelSpace a b t :=
  (signedBilin a b t).ker.mkQ (Pi.single i 1)

/-- One physical quotient-code readout for each subspace of the intrinsic
radical quotient. No ambient genus cap and no supplied intersection labels. -/
private theorem literal_universal_signed_bouquet
    (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val) (u v : E → ℝ) (d : ℝ) (hdLoop : d ≠ 0)
    [Fintype (SignedLabelSpace a b t)] [Fintype (Submodule K (SignedLabelSpace a b t))]
    [∀ L : Submodule K (SignedLabelSpace a b t),
      Fintype (Module.Dual K (SignedLabelSpace a b t ⧸ L))] :
    ∃ α : Submodule K (SignedLabelSpace a b t) → ℝ,
    d*(∑ T : Finset E, inverse (signedCoeff (intrinsicLabel a b t) α) T*
      (∏ e : E, (v e+(d*u e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, u e)*(∏ e ∈ Sᶜ, v e))*d^(signedBouquetCircleCount a b t S) := by
  classical
  let B := signedBilin a b t
  let b' := radicalForm B (signedBilin_symmetric a b t ha hb hd hord)
  exact literal_signed_pairing_walsh a b t (intrinsicLabel a b t) b' ha hb hd hord
    (fun i j => (radicalForm_apply _ _ _ _).trans (signedBilin_port a b t i j)) u v d hdLoop

/-- Canonical finite carriers of the intrinsic label quotient, not a
restriction on the topology or on the band matching. -/
noncomputable def intrinsicFinite (a b : E → D n) (t : E → Bool) :
    Fintype (SignedLabelSpace a b t) := by
  letI : Finite (SignedLabelSpace a b t) :=
    Finite.of_surjective _ (signedBilin a b t).ker.mkQ_surjective
  exact Fintype.ofFinite _

noncomputable def intrinsicSubspaces (a b : E → D n) (t : E → Bool) :
    Fintype (Submodule K (SignedLabelSpace a b t)) := by
  letI := intrinsicFinite a b t
  letI : Finite (Submodule K (SignedLabelSpace a b t)) :=
    Finite.of_injective (fun W : Submodule K (SignedLabelSpace a b t) => (W : Set (SignedLabelSpace a b t)))
      SetLike.coe_injective
  exact Fintype.ofFinite _

noncomputable def intrinsicDuals (a b : E → D n) (t : E → Bool)
    (L : Submodule K (SignedLabelSpace a b t)) :
    Fintype (Module.Dual K (SignedLabelSpace a b t ⧸ L)) := by
  letI := intrinsicFinite a b t
  letI : Finite (SignedLabelSpace a b t ⧸ L) :=
    Finite.of_surjective _ L.mkQ_surjective
  letI : Finite (Module.Dual K (SignedLabelSpace a b t ⧸ L)) :=
    Finite.of_injective (fun f : Module.Dual K (SignedLabelSpace a b t ⧸ L) => fun x => f x)
      (fun {_ _} h => LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

set_option maxHeartbeats 800000 in
theorem literal_intrinsic_signed_bouquet
    (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i ≠ b j)
    (hord : ∀ i, (a i).val < (b i).val) (u v : E → ℝ) (d : ℝ) (hdLoop : d ≠ 0) :
    letI := intrinsicSubspaces a b t
    letI := intrinsicDuals a b t
    ∃ α : Submodule K (SignedLabelSpace a b t) → ℝ,
    d*(∑ T : Finset E, inverse (signedCoeff (intrinsicLabel a b t) α) T*
      (∏ e : E, (v e+(d*u e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, u e)*(∏ e ∈ Sᶜ, v e))*d^(signedBouquetCircleCount a b t S) := by
  letI := intrinsicFinite a b t
  exact @literal_universal_signed_bouquet n E _ _ a b t ha hb hd hord u v d hdLoop
    (intrinsicFinite a b t) (intrinsicSubspaces a b t) (intrinsicDuals a b t)

#print axioms literal_intrinsic_signed_bouquet
#print axioms signedBilin_symmetric
#print axioms radicalForm_apply
#print axioms literal_universal_signed_bouquet
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
