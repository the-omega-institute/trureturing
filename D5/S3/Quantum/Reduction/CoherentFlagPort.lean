/- GID: D5/S3/Quantum/Reduction/CoherentFlagPort
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/CoherentFlagPort
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual finite classical flags and coherent blocks impose component dimension lower bounds and provide complete complement-filled decoders. -/

import D5.S3.Quantum.Reduction.ProbeComponentRigidity

/-!
# Finite flagged coherent ports

An encoder branch and a decoder branch are rectangular Kraus maps. The flag is
retained classically, with no input-dependent quantum bypass. Encoder
normalization is joint over flags; decoder normalization holds separately on
every entire port block. Thus flag probabilities may depend on the input.

Bluhm--Rauber--Wolf, arXiv:1708.04898v4, Sections 4 and 7.1 supplies the
measurement-relative compression model and maximal-block padding construction.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Reduction.CoherentFlagPort
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Reduction.ProbeComponentRigidity
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {d q F a b : Type*} [Fintype d] [DecidableEq d]
  [Fintype q] [DecidableEq q] [Fintype F] [Fintype a] [Fintype b]

/-- One actual finite classical-quantum port. The quantum index q is the only
    input-dependent quantum system available to the decoder. -/
structure FlagPort (d q F a b : Type*) [Fintype d] [DecidableEq d]
    [Fintype q] [DecidableEq q] [Fintype F] [Fintype a] [Fintype b] where
  encode : F → a → Matrix q d ℂ
  decode : F → b → Matrix d q ℂ
  encode_normalized : (∑ f, ∑ k, (encode f k)ᴴ * encode f k) = 1
  decode_normalized : ∀ f, (∑ k, (decode f k)ᴴ * decode f k) = 1

/-- Encoder Kraus matrices with the classical flag stored in mutually
    orthogonal port sectors. Cross-flag quantum coherences are never encoded. -/
def FlagPort.encoderKraus [DecidableEq F] (P : FlagPort d q F a b)
    (k : F × a) : Matrix (F × q) d ℂ :=
  fun i j => if i.1 = k.1 then P.encode k.1 k.2 i.2 j else 0

/-- Decoder Kraus matrices read one classical sector and discard all
    cross-sector coherences on the ambient flagged matrix algebra. -/
def FlagPort.decoderKraus [DecidableEq F] (P : FlagPort d q F a b)
    (k : F × b) : Matrix d (F × q) ℂ :=
  fun i j => if j.1 = k.1 then P.decode k.1 k.2 i j.2 else 0

private theorem encoder_normalized [DecidableEq F] (P : FlagPort d q F a b) :
    (∑ k, (P.encoderKraus k)ᴴ * P.encoderKraus k) = 1 := by
  ext i j
  simpa [FlagPort.encoderKraus, Fintype.sum_prod_type, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply] using
    congrArg (fun M : Matrix d d ℂ => M i j) P.encode_normalized

private theorem decoder_normalized [DecidableEq F] (P : FlagPort d q F a b) :
    (∑ k, (P.decoderKraus k)ᴴ * P.decoderKraus k) = 1 := by
  ext i j
  rcases i with ⟨f, i⟩
  rcases j with ⟨g, j⟩
  by_cases h : f = g
  · subst g
    simpa [FlagPort.decoderKraus, Fintype.sum_prod_type, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix q q ℂ => M i j) (P.decode_normalized f)
  · simp only [FlagPort.decoderKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    have hz (k : F) (l : b) (m : d) :
        star (if f = k then P.decode k l m i else 0) *
          (if g = k then P.decode k l m j else 0) = 0 := by
      by_cases hf : f = k
      · subst k
        simp [Ne.symm h]
      · simp [hf]
    simp only [hz, Finset.sum_const_zero]
    simp [Matrix.one_apply, h]

/-- Composite Kraus operator, using the same actual flag on both sides. -/
def FlagPort.kraus (P : FlagPort d q F a b) (r : F × b × a) : Matrix d d ℂ :=
  P.decode r.1 r.2.1 * P.encode r.1 r.2.2

private theorem port_normalized (P : FlagPort d q F a b) :
    (∑ r, (P.kraus r)ᴴ * P.kraus r) = 1 := by
  simp only [FlagPort.kraus, Fintype.sum_prod_type, conjTranspose_mul, Matrix.mul_assoc]
  calc
    (∑ f, ∑ k, ∑ l,
      (P.encode f l)ᴴ * ((P.decode f k)ᴴ * (P.decode f k * P.encode f l))) =
      ∑ f, ∑ l, (P.encode f l)ᴴ *
        (∑ k, (P.decode f k)ᴴ * P.decode f k) * P.encode f l := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.sum_comm]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = 1 := by simp only [P.decode_normalized, Matrix.mul_one]; exact P.encode_normalized

private theorem flagged_kraus_product [DecidableEq F] (P : FlagPort d q F a b)
    (r : F × b) (t : F × a) :
    P.decoderKraus r * P.encoderKraus t =
      if r.1 = t.1 then P.decode r.1 r.2 * P.encode t.1 t.2 else 0 := by
  rcases r with ⟨f, k⟩
  rcases t with ⟨g, l⟩
  ext i j
  by_cases h : f = g
  · subst g
    simp [FlagPort.encoderKraus, FlagPort.decoderKraus, Matrix.mul_apply,
      Fintype.sum_prod_type]
  · simp only [FlagPort.encoderKraus, FlagPort.decoderKraus, Matrix.mul_apply,
      Fintype.sum_prod_type, h, if_false, Matrix.zero_apply]
    have hz (c : F) (m : q) :
        (if c = f then P.decode f k i m else 0) *
          (if c = g then P.encode g l m j else 0) = 0 := by
      by_cases hc : c = f
      · subst c
        simp [h]
      · simp [hc]
    simp only [hz, Finset.sum_const_zero]

/-- The rectangular port model is realized by actual canonical CPTP maps.
    Their all-matrix round trip uses exactly the same finite classical flag;
    no independent flag choices or quantum bypass enter the composite. -/
theorem flagged_cptp_roundtrip [DecidableEq F] (P : FlagPort d q F a b) :
    ∃ E : QuantumChannel d (F × q), ∃ D : QuantumChannel (F × q) d,
      (∀ X : Matrix d d ℂ, ∀ f g : F, f ≠ g → ∀ i j : q,
        CStarMatrix.ofMatrix.symm
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) (f,i) (g,j) = 0) ∧
      ∀ X : Matrix d d ℂ,
        CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
        ∑ k, P.kraus k * X * (P.kraus k)ᴴ := by
  obtain ⟨E, hE⟩ := finite_kraus_quantum_channel P.encoderKraus (encoder_normalized P)
  obtain ⟨D, hD⟩ := finite_kraus_quantum_channel P.decoderKraus (decoder_normalized P)
  refine ⟨E, D, ?_, fun X => ?_⟩
  · intro X f g hfg i j
    rw [hE]
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    rintro ⟨c, k⟩ hk
    by_cases hf : f = c
    · subst c
      simp [FlagPort.encoderKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Ne.symm hfg]
    · simp [FlagPort.encoderKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, hf]
  · have he : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) =
        CStarMatrix.ofMatrix (∑ k, P.encoderKraus k * X * (P.encoderKraus k)ᴴ) := by
      exact CStarMatrix.ofMatrix.symm.injective (by simpa only [Equiv.symm_apply_apply] using hE X)
    rw [he, hD]
    calc
      _ = ∑ r, ∑ t, (P.decoderKraus r * P.encoderKraus t) * X *
          (P.decoderKraus r * P.encoderKraus t)ᴴ := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
          Matrix.mul_assoc]
      _ = _ := by
        simp [flagged_kraus_product, Fintype.sum_prod_type, FlagPort.kraus]

/-- A whole-block decoder for a partial isometry, with a fixed density supported
    in the output component. The reset columns may be any finite factorization
    of that density. -/
def paddedDecoder {r : Type*} [Fintype r]
    (J : Matrix q d ℂ) (u : r → d → ℂ) : Unit ⊕ (r × q) → Matrix d q ℂ :=
  Sum.elim (fun _ => Jᴴ)
    (fun k => vecMulVec (u k.1) (fun i => ((1 : Matrix q q ℂ) - J * Jᴴ) k.2 i))

private theorem reset_gram {r : Type*} [Fintype r]
    (u : r → d → ℂ) (hu : (∑ k, star (u k) ⬝ᵥ u k) = 1)
    (Q : Matrix q q ℂ) :
    (∑ k : r × q,
      (vecMulVec (u k.1) (fun i => Q k.2 i))ᴴ *
        vecMulVec (u k.1) (fun i => Q k.2 i)) = Qᴴ * Q := by
  ext i j
  simp only [Matrix.sum_apply]
  change (∑ k : r × q, ∑ m : d,
    star (u k.1 m * Q k.2 i) * (u k.1 m * Q k.2 j)) =
      ∑ l : q, star (Q l i) * Q l j
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ l : q, (∑ k : r, ∑ m : d, star (u k m) * u k m) *
        (star (Q l i) * Q l j) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [star_mul]
      ring
    _ = _ := by
      change (∑ k : r, ∑ m : d, star (u k m) * u k m) = 1 at hu
      rw [hu]
      simp only [one_mul]

private theorem reset_action {r : Type*} [Fintype r]
    (u : r → d → ℂ) (Q : Matrix q q ℂ) (Y : Matrix q q ℂ) :
    (∑ k : r × q,
      vecMulVec (u k.1) (fun i => Q k.2 i) * Y *
        (vecMulVec (u k.1) (fun i => Q k.2 i))ᴴ) =
      trace (Q * Y * Qᴴ) • (∑ k, probe (u k)) := by
  have hkl (k : r) (l : q) :
      vecMulVec (u k) (fun i => Q l i) * Y *
        (vecMulVec (u k) (fun i => Q l i))ᴴ =
      (Q * Y * Qᴴ) l l • probe (u k) := by
    ext i j
    change (∑ n : q, (∑ m : q, u k i * Q l m * Y m n) *
      star (u k j * Q l n)) =
      (∑ n : q, (∑ m : q, Q l m * Y m n) * star (Q l n)) *
        (u k i * star (u k j))
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    simp only [star_mul]
    ring
  simp only [Fintype.sum_prod_type, hkl]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Finset.smul_sum]
  rfl

private theorem scalar_component_rank (C : Matrix d d ℂ)
    (S : Submodule ℂ (d → ℂ)) (coeff : ℂ) (hcoeff : coeff ≠ 0)
    (h : ∀ x ∈ S, C *ᵥ x = coeff • x) : Module.finrank ℂ S ≤ C.rank := by
  have hs : S ≤ LinearMap.range C.mulVecLin := by
    intro x hx
    refine ⟨coeff⁻¹ • x, ?_⟩
    change C *ᵥ (coeff⁻¹ • x) = x
    rw [mulVec_smul, h x hx, smul_smul, inv_mul_cancel₀ hcoeff, one_smul]
  exact Submodule.finrank_mono hs

private theorem nonzero_probe_scalar {s : Type*} [Fintype s]
    (K : s → Matrix d d ℂ) (hTP : (∑ k, (K k)ᴴ * K k) = 1)
    (v : d → ℂ) (hv : star v ⬝ᵥ v = 1)
    (he : ∀ k, K k *ᵥ v = probeScalar (K k) v • v) :
    ∃ k, probeScalar (K k) v ≠ 0 := by
  by_contra hn
  have hz : ∀ k, K k *ᵥ v = 0 := by
    intro k
    rw [he, not_exists.mp hn k |> not_not.mp, zero_smul]
  have h := congrArg (fun M : Matrix d d ℂ => M *ᵥ v) hTP
  simp only [Matrix.sum_mulVec, ← mulVec_mulVec, hz, mulVec_zero, Finset.sum_const_zero,
    one_mulVec] at h
  simp [← h] at hv

/-- Any actual finite flagged port preserving all probe probabilities has a
    coherent block at least as large as every nonorthogonality component. -/
theorem port_component_lower_bound {J : Type*} (P : FlagPort d q F a b)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ k,
        P.kraus k * CStarMatrix.ofMatrix.symm ρ.1 * (P.kraus k)ᴴ)) =
      trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    ∀ j, Module.finrank ℂ (componentSpace v j) ≤ Fintype.card q := by
  have hs := kraus_scalar_on_component P.kraus (port_normalized P) v hv hprob
  intro j
  have hm : v j ∈ componentSpace v j :=
    Submodule.subset_span ⟨j, Relation.EqvGen.refl j, rfl⟩
  obtain ⟨k, hk⟩ := nonzero_probe_scalar P.kraus (port_normalized P)
    (v j) (hv j) (fun k => hs k j (v j) hm)
  exact (scalar_component_rank (P.kraus k) (componentSpace v j)
    (probeScalar (P.kraus k) (v j)) hk (hs k j)).trans
    (((Matrix.rank_mul_le _ _).trans (min_le_left _ _)).trans (Matrix.rank_le_card_width _))

private theorem partial_isometry (J : Matrix q d ℂ) (P : Matrix d d ℂ)
    (hJ : Jᴴ * J = P) (hP : Pᴴ = P) (hPP : P * P = P) : J * P = J := by
  have hz : (J - J * P)ᴴ * (J - J * P) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_mul, hP, Matrix.sub_mul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hJ, hPP]
    simp only [Matrix.mul_assoc, hJ, hPP]
    abel
  exact (sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hz)).symm

/-- The complement-filled decoder is normalized on the entire coherent block,
    and its action is exactly the support inverse plus a fixed-state filler. -/
theorem padded_decoder_cptp {r : Type*} [Fintype r]
    (J : Matrix q d ℂ) (P : Matrix d d ℂ)
    (hJ : Jᴴ * J = P) (hP : Pᴴ = P) (hPP : P * P = P)
    (u : r → d → ℂ) (hu : (∑ k, star (u k) ⬝ᵥ u k) = 1) :
    (∑ k, (paddedDecoder J u k)ᴴ * paddedDecoder J u k) = 1 ∧
    ∃ T : QuantumChannel q d, ∀ Y : Matrix q q ℂ,
      CStarMatrix.ofMatrix.symm
        (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) =
      Jᴴ * Y * J + trace ((1 - J * Jᴴ) * Y) • (∑ k, probe (u k)) := by
  have hJP := partial_isometry J P hJ hP hPP
  let Q := J * Jᴴ
  have hQ : Qᴴ = Q := by simp [Q]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ, hJ, ← Matrix.mul_assoc, hJP]
  have hR : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
    simp [conjTranspose_sub, hQ, Matrix.sub_mul, Matrix.mul_sub, hQQ]
  have ht : (∑ k, (paddedDecoder J u k)ᴴ * paddedDecoder J u k) = 1 := by
    simp only [paddedDecoder, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fintype.sum_unique, conjTranspose_conjTranspose]
    rw [reset_gram u hu, hR]
    dsimp [Q]
    abel
  refine ⟨ht, ?_⟩
  obtain ⟨T, hT⟩ := finite_kraus_quantum_channel (paddedDecoder J u) ht
  refine ⟨T, fun Y => ?_⟩
  rw [hT]
  simp only [paddedDecoder, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique, conjTranspose_conjTranspose]
  rw [reset_action]
  congr 2
  rw [trace_mul_comm, ← Matrix.mul_assoc]
  change trace ((1 - Q)ᴴ * (1 - Q) * Y) = trace ((1 - Q) * Y)
  rw [hR]

/-- The explicit decoder recovers the entire component corner, with no
    unnormalized or undefined action on the unused port complement. -/
theorem padded_decoder_corner {r : Type*} [Fintype r]
    (J : Matrix q d ℂ) (P : Matrix d d ℂ)
    (hJ : Jᴴ * J = P) (hP : Pᴴ = P) (hPP : P * P = P)
    (u : r → d → ℂ) (X : Matrix d d ℂ) :
    (∑ k, paddedDecoder J u k * (J * X * Jᴴ) * (paddedDecoder J u k)ᴴ) =
      P * X * P := by
  have hJP := partial_isometry J P hJ hP hPP
  have hQJ : (1 - J * Jᴴ) * J = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hJ, hJP, sub_self]
  simp only [paddedDecoder, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique, conjTranspose_conjTranspose]
  rw [reset_action]
  have hz : (1 - J * Jᴴ) * (J * X * Jᴴ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQJ, Matrix.zero_mul, Matrix.zero_mul]
  rw [hz, Matrix.zero_mul, trace_zero, zero_smul, add_zero]
  simp only [← Matrix.mul_assoc, hJ]
  simp only [Matrix.mul_assoc, hJ]

/-- The measured component encoder and the complete padded decoders form a
    single actual port; the composite is exactly the component pinching map. -/
theorem component_pinching_port {r : Type*} [Fintype r]
    (J : F → Matrix q d ℂ) (P : F → Matrix d d ℂ)
    (hJ : ∀ f, (J f)ᴴ * J f = P f)
    (hP : ∀ f, (P f)ᴴ = P f) (hPP : ∀ f, P f * P f = P f)
    (hfull : (∑ f, P f) = 1)
    (u : F → r → d → ℂ) (hu : ∀ f, (∑ k, star (u f k) ⬝ᵥ u f k) = 1) :
    ∃ port : FlagPort d q F Unit (Unit ⊕ (r × q)),
      (∀ f, port.encode f () = J f) ∧
      (∀ f k, port.decode f k = paddedDecoder (J f) (u f) k) ∧
      ∀ X : Matrix d d ℂ, (∑ k, port.kraus k * X * (port.kraus k)ᴴ) =
        ∑ f, P f * X * P f := by
  let port : FlagPort d q F Unit (Unit ⊕ (r × q)) :=
    { encode := fun f _ => J f
      decode := fun f k => paddedDecoder (J f) (u f) k
      encode_normalized := by simpa only [Fintype.sum_unique, hJ] using hfull
      decode_normalized := fun f =>
        (padded_decoder_cptp (J f) (P f) (hJ f) (hP f) (hPP f) (u f) (hu f)).1 }
  refine ⟨port, fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro X
  simp only [FlagPort.kraus, Fintype.sum_prod_type, Fintype.sum_unique,
    conjTranspose_mul]
  dsimp only [port]
  apply Finset.sum_congr rfl
  intro f hf
  simpa only [Matrix.mul_assoc] using
    padded_decoder_corner (J f) (P f) (hJ f) (hP f) (hPP f) (u f) X

#print axioms flagged_cptp_roundtrip
#print axioms component_pinching_port
#print axioms port_component_lower_bound
#print axioms padded_decoder_cptp
#print axioms padded_decoder_corner
end D5.S3.Quantum.Reduction.CoherentFlagPort
