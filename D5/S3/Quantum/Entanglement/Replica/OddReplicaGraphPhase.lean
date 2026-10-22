/- GID: D5/S3/Quantum/Entanglement/Replica/OddReplicaGraphPhase
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Replica/OddReplicaGraphPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized graph forms give literal binary replica character sums. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
import D5.S3.Fourier.RepresentativeOrbitCoordinates
import D5.S3.Fourier.CharacterOrbitField
import D5.S3.QuadraticForms.FiniteHermitianCharacterSum
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound

/-! The literal graph phase and its finite-field Fourier transport. -/

open scoped BigOperators
open Function

namespace D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase

open Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient

noncomputable section

/-- The replica displacement of a qubit; the last party has displacement zero. -/
def displacement {N q : ℕ} (n : ℕ) (col : Fin N → Fin q) (u : Fin N) :
    Fin (q - 1) → ZMod n :=
  fun i => if (i : ℕ) = (col u : ℕ) then 1 else 0

/-- The binary graph phase on all literal replica configurations. -/
def phase {N d n : ℕ} [NeZero n] (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) : ZMod 2 :=
  ∑ r, ∑ u, ∑ v, if u < v then
    A u v * (x r u * x r v + x (r + δ u) u * x (r + δ v) v) else 0

private lemma shift_displacement {N q n : ℕ} (col : Fin N → Fin q)
    (u : Fin N) (r : Fin (q - 1) → ZMod n) :
    shift n q (col u) r = r + displacement n col u := by
  ext i
  simp only [StabilizerMultiEntropyCollapse.shift, displacement, Pi.add_apply]
  split <;> simp

/-- Expanding the literal graph amplitudes at any replica index gives the graph phase. -/
private theorem graph_replica_phase {N q : ℕ} (n : ℕ) [NeZero n]
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (col : Fin N → Fin q) :
    Z n q col (graphAmp A) =
      ∑ x : (Fin (q - 1) → ZMod n) → Fin N → ZMod 2,
        complexSign (phase A (displacement n col) x) := by
  classical
  have hg (v : Fin N → ZMod 2) :
      graphAmp A v = complexSign (∑ u, ∑ w, if u < w then A u w * v u * v w else 0) := by
    simp only [graphAmp, normalExponent, Finset.sum_filter]
    exact (complex_sign_val _).symm
  have hs (t : ZMod 2) : star (complexSign t) = complexSign t := by
    rw [complexSign]
    split <;> norm_num
  change (∑ x : (Fin (q - 1) → ZMod n) → Fin N → ZMod 2,
    ∏ r : (Fin (q - 1) → ZMod n), star (graphAmp A (x r)) *
      graphAmp A (fun u => x (shift n q (col u) r) u)) = _
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [hg, hs, ← complexSign_add, shift_displacement]
  rw [← sign_sum]
  congr 1
  simp only [phase, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split <;> ring

/-- Every supplied normalized local-unitary graph form has its literal normalized phase sum. -/
private theorem actual_graph_replica_phase {N q : ℕ} (n : ℕ) [NeZero n]
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hform : ψ = c • (tensorOp U *ᵥ graphAmp A))
    (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1) :
    Z n q col ψ = ((2 : ℂ) ^ (N * n ^ (q - 1)))⁻¹ *
      ∑ x : (Fin (q - 1) → ZMod n) → Fin N → ZMod 2,
        complexSign (phase A (displacement n col) x) := by
  subst ψ
  rw [Z_local_scalar n q col (graphAmp A) U hU c, Z_smul,
    graph_scalar_norm A U hU c hnorm, graph_replica_phase]
  rw [inv_pow, ← pow_mul]

section Fourier

variable {n d : ℕ} [NeZero n] {F : Type*} [Field F] [CharP F 2]

/-- The actual character indexed by `t`, with a supplied primitive-root power law. -/
def character (ζ : F) (hζ : ζ ^ n = 1) (t : Fin d → ZMod n) :
    AddChar (Fin d → ZMod n) F where
  toFun r := AddChar.zmodChar n hζ (∑ i, t i * r i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' r s := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact AddChar.map_add_eq_mul _ _ _

/-- Unnormalized finite-field Fourier coefficients. -/
def fourier (ζ : F) (hζ : ζ ^ n = 1) (a : (Fin d → ZMod n) → F)
    (t : Fin d → ZMod n) : F :=
  ∑ r, a r * character ζ hζ t r

/-- The literal character component of the binary graph phase. -/
def phaseComponent {N : ℕ} (ζ : F) (hζ : ζ ^ n = 1)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) (t : Fin d → ZMod n) : F :=
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  ∑ u : Fin N, ∑ v : Fin N, if u < v then
    algebraMap (ZMod 2) F (A u v) * (1 + character ζ hζ t (δ v - δ u)) *
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (x r u)) t *
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (x r v)) (-t) else 0

private lemma character_symm (ζ : F) (hζ : ζ ^ n = 1) (t r : Fin d → ZMod n) :
    character ζ hζ t r = character ζ hζ r t := by
  change AddChar.zmodChar n hζ (∑ i, t i * r i) =
    AddChar.zmodChar n hζ (∑ i, r i * t i)
  simp only [mul_comm]

private lemma character_neg (ζ : F) (hζ : ζ ^ n = 1) (t r : Fin d → ZMod n) :
    character ζ hζ (-t) r = character ζ hζ t (-r) := by
  change AddChar.zmodChar n hζ (∑ i, -(t i) * r i) =
    AddChar.zmodChar n hζ (∑ i, t i * -(r i))
  simp only [neg_mul, mul_neg]

private lemma character_orthogonal (ζ : F) (hζ : IsPrimitiveRoot ζ n) (ho : Odd n)
    (t : Fin d → ZMod n) :
    (∑ r, character ζ hζ.pow_eq_one t r) = if t = 0 then 1 else 0 := by
  classical
  have htrivial : character ζ hζ.pow_eq_one t = 0 ↔ t = 0 := by
    constructor
    · intro ht
      funext i
      have hi := congrArg (fun χ : AddChar (Fin d → ZMod n) F => χ (Pi.single i 1)) ht
      have hi' : ζ ^ (t i).val = 1 := by
        simpa [character, Pi.single_apply, AddChar.zmodChar_apply] using hi
      exact (ZMod.val_eq_zero _).mp
        (hζ.pow_inj (ZMod.val_lt _) (NeZero.pos _) (hi'.trans (pow_zero ζ).symm))
    · intro ht
      subst t
      ext r
      simp [character]
  have hnF : (n : F) = 1 := natCast_eq_one_of_odd_of_two_eq_zero ho CharTwo.two_eq_zero
  simp only [AddChar.sum_eq_ite, htrivial, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, Nat.cast_pow, hnF, one_pow]

private lemma fourier_parseval (ζ : F) (hζ : IsPrimitiveRoot ζ n) (ho : Odd n)
    (a b : (Fin d → ZMod n) → F) :
    (∑ t, fourier ζ hζ.pow_eq_one a t * fourier ζ hζ.pow_eq_one b (-t)) =
      ∑ r, a r * b r := by
  classical
  let χ := character (d := d) ζ hζ.pow_eq_one
  have hc (t r s : Fin d → ZMod n) : χ t r * χ (-t) s = χ (r - s) t := by
    rw [character_neg, ← AddChar.map_add_eq_mul, character_symm]
    simp only [χ, sub_eq_add_neg]
  calc
    _ = ∑ t, ∑ r, ∑ s, (a r * χ t r) * (b s * χ (-t) s) := by
      apply Finset.sum_congr rfl
      intro t _
      unfold fourier
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = ∑ r, ∑ s, a r * b s * (∑ t, χ (r - s) t) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      change (a r * χ t r) * (b s * χ (-t) s) = _
      rw [show (a r * χ t r) * (b s * χ (-t) s) =
        (a r * b s) * (χ t r * χ (-t) s) by ring, hc]
    _ = _ := by
      simp only [χ, character_orthogonal ζ hζ ho, sub_eq_zero]
      simp

private lemma fourier_shift (ζ : F) (hζ : ζ ^ n = 1)
    (a : (Fin d → ZMod n) → F) (s t : Fin d → ZMod n) :
    fourier ζ hζ (fun r => a (r + s)) t =
      character ζ hζ t (-s) * fourier ζ hζ a t := by
  classical
  simp only [fourier, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.addRight s)
  intro r
  dsimp
  rw [AddChar.map_add_eq_mul]
  have hc : character ζ hζ t (-s) * character ζ hζ t s = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  calc
    a (r + s) * character ζ hζ t r =
      (character ζ hζ t (-s) * character ζ hζ t s) *
        (a (r + s) * character ζ hζ t r) := by rw [hc, one_mul]
    _ = character ζ hζ t (-s) *
      (a (r + s) * (character ζ hζ t r * character ζ hζ t s)) := by ring

/-- The actual binary phase is transported to all characters at every odd index. -/
private theorem phase_fourier {N : ℕ} (ζ : F) (hζ : IsPrimitiveRoot ζ n) (ho : Odd n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    algebraMap (ZMod 2) F (phase A δ x) =
      ∑ t : Fin d → ZMod n, ∑ u : Fin N, ∑ v : Fin N, if u < v then
        algebraMap (ZMod 2) F (A u v) *
          (1 + character ζ hζ.pow_eq_one t (δ v - δ u)) *
          fourier ζ hζ.pow_eq_one (fun r => algebraMap (ZMod 2) F (x r u)) t *
          fourier ζ hζ.pow_eq_one (fun r => algebraMap (ZMod 2) F (x r v)) (-t)
        else 0 := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let χ := character (d := d) ζ hζ.pow_eq_one
  let X (u : Fin N) (r : Fin d → ZMod n) : F := algebraMap (ZMod 2) F (x r u)
  have hedge (u v : Fin N) :
      (∑ r, (X u r * X v r + X u (r + δ u) * X v (r + δ v))) =
      ∑ t, (1 + χ t (δ v - δ u)) *
        fourier ζ hζ.pow_eq_one (X u) t * fourier ζ hζ.pow_eq_one (X v) (-t) := by
    rw [Finset.sum_add_distrib, ← fourier_parseval ζ hζ ho (X u) (X v),
      ← fourier_parseval ζ hζ ho (fun r => X u (r + δ u)) (fun r => X v (r + δ v)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [fourier_shift, fourier_shift, character_neg]
    simp only [neg_neg]
    have hchar : χ t (-δ u) * χ t (δ v) = χ t (δ v - δ u) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    change _ + (χ t (-δ u) * _) * (χ t (δ v) * _) = _
    linear_combination
      fourier ζ hζ.pow_eq_one (X u) t * fourier ζ hζ.pow_eq_one (X v) (-t) * hchar
  simp only [phase, map_sum, apply_ite, map_mul, map_add, map_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · simp only [huv, ite_true]
    calc
      _ = algebraMap (ZMod 2) F (A u v) *
          (∑ r, (X u r * X v r + X u (r + δ u) * X v (r + δ v))) := by
        rw [Finset.mul_sum]
      _ = algebraMap (ZMod 2) F (A u v) *
          (∑ t, (1 + χ t (δ v - δ u)) *
            fourier ζ hζ.pow_eq_one (X u) t * fourier ζ hζ.pow_eq_one (X v) (-t)) := by
        rw [hedge]
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]; rfl
  · simp [huv]

private lemma phase_component_frobenius {N : ℕ} (ζ : F) (hζ : ζ ^ n = 1)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) (t : Fin d → ZMod n) :
    phaseComponent ζ hζ A δ x (fun i => 2 * t i) =
      (phaseComponent ζ hζ A δ x t)^2 := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let χ := character (d := d) ζ hζ
  have hchar (s r : Fin d → ZMod n) : χ (fun i => 2 * s i) r = (χ s r)^2 := by
    change AddChar.zmodChar n hζ (∑ i, (2 * s i) * r i) =
      (AddChar.zmodChar n hζ (∑ i, s i * r i))^2
    rw [show (∑ i, (2 * s i) * r i) = 2 * ∑ i, s i * r i by
      simp only [Finset.mul_sum, mul_assoc]]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      (AddChar.zmodChar n hζ).map_nsmul_eq_pow 2 (∑ i, s i * r i)
  have hbin (a : ZMod 2) : (algebraMap (ZMod 2) F a)^2 = algebraMap (ZMod 2) F a := by
    rw [← map_pow, ZMod.pow_card]
  have hhat (a : (Fin d → ZMod n) → ZMod 2) (s : Fin d → ZMod n) :
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) (fun i => 2 * s i) =
        (fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) s)^2 := by
    change _ = frobenius F 2 _
    simp only [fourier, map_sum, map_mul, frobenius_def, hbin]
    apply Finset.sum_congr rfl
    intro r _
    rw [show character ζ hζ (fun i => 2 * s i) r = (character ζ hζ s r)^2 from hchar s r]
  have hneg : -(fun i => (2 : ZMod n) * t i) = (fun i => 2 * (-t) i) := by
    ext i
    exact (mul_neg _ _).symm
  change _ = frobenius F 2 _
  simp only [phaseComponent, map_sum, apply_ite, map_mul, map_add, map_one, map_zero,
    frobenius_def, hbin]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · rw [hhat, hneg, hhat]
    rw [show character ζ hζ (fun i => 2 * t i) (δ v - δ u) =
      (character ζ hζ t (δ v - δ u))^2 from hchar _ _]
  · rfl

private lemma character_product (ζ : F) (hζ : ζ ^ n = 1) (t r : Fin d → ZMod n) :
    character ζ hζ t r = ∏ i : Fin d, (ζ ^ (t i).val)^(r i).val := by
  classical
  change AddChar.zmodChar n hζ (∑ i, t i * r i) = _
  rw [show AddChar.zmodChar n hζ (∑ i, t i * r i) =
    ∏ i, AddChar.zmodChar n hζ (t i * r i) from
    congrArg Additive.toMul (map_sum (AddChar.zmodChar n hζ).toAddMonoidHom _
      Finset.univ) |>.trans (toMul_sum _ _)]
  apply Finset.prod_congr rfl
  intro i _
  change AddChar.zmodChar n hζ (t i * r i) =
    (AddChar.zmodChar n hζ (t i)) ^ (r i).val
  rw [← (AddChar.zmodChar n hζ).map_nsmul_eq_pow]
  congr 1
  simp [nsmul_eq_mul, mul_comm]

private lemma character_mem (ζ : F) (hζ : ζ ^ n = 1) (t r : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    character ζ hζ t r ∈ IntermediateField.adjoin (ZMod 2)
      (Set.range (fun i : Fin d => ζ ^ (t i).val)) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  have he := character_product ζ hζ t r
  rw [he]
  apply IntermediateField.prod_mem
  intro i _
  exact _root_.pow_mem (IntermediateField.subset_adjoin (ZMod 2)
    (Set.range (fun i : Fin d => ζ ^ (t i).val)) ⟨i, rfl⟩) _

private lemma phase_component_mem {N : ℕ} (ζ : F) (hζ : ζ ^ n = 1)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) (t : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    phaseComponent ζ hζ A δ x t ∈ IntermediateField.adjoin (ZMod 2)
      (Set.range (fun i : Fin d => ζ ^ (t i).val)) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  have hχmem (r : Fin d → ZMod n) : character ζ hζ t r ∈ K :=
    character_mem ζ hζ t r
  have hhatmem (a : (Fin d → ZMod n) → ZMod 2) :
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) t ∈ K := by
    apply IntermediateField.sum_mem
    intro r _
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) (hχmem r)
  have hhatneg (a : (Fin d → ZMod n) → ZMod 2) :
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) (-t) ∈ K := by
    apply IntermediateField.sum_mem
    intro r _
    apply IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
    rw [character_neg]
    exact hχmem (-r)
  apply IntermediateField.sum_mem
  intro u _
  apply IntermediateField.sum_mem
  intro v _
  split_ifs
  · exact IntermediateField.mul_mem _
      (IntermediateField.mul_mem _
        (IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
          (IntermediateField.add_mem _ (IntermediateField.one_mem _) (hχmem _)))
        (hhatmem _)) (hhatneg _)
  · exact IntermediateField.zero_mem _

/-- The contribution of an actual doubling orbit is its actual prime-field trace. -/
private theorem actual_orbit_phase_trace {N : ℕ} (hn : 3 ≤ n) (ho : Odd n) [Finite F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) (t : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let p : Equiv.Perm (Fin d → ZMod n) := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
    ∃ y : K, (y : F) = phaseComponent ζ hζ.pow_eq_one A δ x t ∧
      algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) K y) =
        ∑ l ∈ Finset.range (minimalPeriod (p : _ → _) t),
          phaseComponent ζ hζ.pow_eq_one A δ x ((p : _ → _)^[l] t) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let G := Fin d → ZMod n
  let p : Equiv.Perm G := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  let f := phaseComponent ζ hζ.pow_eq_one A δ x
  let y : K := ⟨f t, phase_component_mem ζ hζ.pow_eq_one A δ x t⟩
  refine ⟨y, rfl, ?_⟩
  have hp (s : G) : p s = fun i => (2 : ZMod n) * s i := by
    funext i
    simp [p, Equiv.piCongrRight, Units.mulLeft, ZMod.coe_unitOfCoprime]
  have hc : Function.Semiconj f (p : G → G) (frobenius F 2) := by
    intro s
    rw [hp]
    exact phase_component_frobenius ζ hζ.pow_eq_one A δ x s
  have hi (l : ℕ) : f ((p : G → G)^[l] t) = (f t)^(2^l) := by
    rw [hc.iterate_right l]
    exact congrFun (coe_iterateFrobenius F 2 l).symm (f t)
  have hd := D5.S3.Fourier.CharacterOrbitField.character_orbit_degree n d hn ho F ζ hζ t
  change Module.finrank (ZMod 2) K = minimalPeriod (p : G → G) t at hd
  have ht := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) (L := K) y
  have ht' := congrArg (algebraMap K F) ht
  simp only [map_sum, map_pow, IsScalarTower.algebraMap_apply, Nat.card_eq_fintype_card,
    ZMod.card] at ht'
  change algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) K y) = _ at ht'
  rw [ht', hd]
  apply Finset.sum_congr rfl
  intro l _
  exact (hi l).symm

/-- The actual mode polynomial as an element of its generated orbit field. -/
def orbitPhase {N : ℕ} (ζ : F) (hζ : ζ ^ n = 1)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) (t : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val)) :=
  ⟨phaseComponent ζ hζ A δ x t, phase_component_mem ζ hζ A δ x t⟩

private theorem phase_orbit_traces {N : ℕ} (hn : 3 ≤ n) (ho : Odd n) [Finite F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (δ : Fin N → (Fin d → ZMod n))
    (x : (Fin d → ZMod n) → Fin N → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    letI : Fintype O := Fintype.ofFinite O
    ∀ sec : O → G, (∀ q, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec q) = q) →
      phase A δ x = ∑ q : O,
        Algebra.trace (ZMod 2) (IntermediateField.adjoin (ZMod 2)
          (Set.range (fun i : Fin d => ζ ^ (sec q i).val)))
          (orbitPhase ζ hζ.pow_eq_one A δ x (sec q)) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let G := Fin d → ZMod n
  let p : Equiv.Perm G := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
  let O := Quotient (Equiv.Perm.SameCycle.setoid p)
  letI : Fintype O := Fintype.ofFinite O
  let qof : G → O := Quotient.mk (Equiv.Perm.SameCycle.setoid p)
  let f := phaseComponent ζ hζ.pow_eq_one A δ x
  dsimp only
  intro sec hsec
  have hfiber (q : O) :
      (∑ l ∈ Finset.range (minimalPeriod (p : G → G) (sec q)), f ((p : G → G)^[l] (sec q))) =
        ∑ s : {s : G // qof s = q}, f s := by
    let k := minimalPeriod (p : G → G) (sec q)
    have hk : 0 < k := minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts _)
    have hm (l : ℕ) : qof ((p : G → G)^[l] (sec q)) = q := by
      calc
        _ = qof (sec q) := (Quotient.sound (show p.SameCycle (sec q) ((p : G → G)^[l] (sec q)) from
          ⟨(l : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]⟩)).symm
        _ = q := hsec q
    let g : Fin k → {s : G // qof s = q} := fun l => ⟨(p : G → G)^[l] (sec q), hm l⟩
    have hg : Function.Bijective g := by
      constructor
      · intro l m h
        apply Fin.ext
        exact (iterate_eq_iterate_iff_of_lt_minimalPeriod l.isLt m.isLt).mp
          (congrArg Subtype.val h)
      · intro s
        have hc : p.SameCycle (sec q) s := Quotient.exact ((hsec q).trans s.property.symm)
        obtain ⟨l, hl⟩ := hc.exists_nat_pow_eq
        have hl' : (p : G → G)^[l] (sec q) = s := by simpa [Equiv.Perm.coe_pow] using hl
        refine ⟨⟨l % k, Nat.mod_lt _ hk⟩, ?_⟩
        apply Subtype.ext
        exact iterate_mod_minimalPeriod_eq.trans hl'
    let e := Equiv.ofBijective g hg
    have he := Equiv.sum_comp e (fun s : {s : G // qof s = q} => f s)
    change (∑ l : Fin k, f ((p : G → G)^[l] (sec q))) = _ at he
    exact (Fin.sum_univ_eq_sum_range
      (fun l : ℕ => f ((p : G → G)^[l] (sec q))) k).symm.trans he
  apply (algebraMap (ZMod 2) F).injective
  rw [phase_fourier ζ hζ ho, map_sum]
  change (∑ t : G, f t) = _
  rw [← Fintype.sum_fiberwise qof f]
  apply Finset.sum_congr rfl
  intro q _
  obtain ⟨y, hy, ht⟩ := actual_orbit_phase_trace hn ho ζ hζ A δ x (sec q)
  have heq : y = orbitPhase ζ hζ.pow_eq_one A δ x (sec q) := Subtype.ext hy
  rw [← heq, ht, hfiber]

/-- Literal normalized graph forms admit the exact sum of actual orbit traces, with every orbit present. -/
private theorem actual_graph_replica_orbit_sum {N q : ℕ} (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) (ho : Odd n) (F : Type*) [Field F] [Finite F] [CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hform : ψ = c • (tensorOp U *ᵥ graphAmp A))
    (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin (q - 1) → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    letI : Fintype O := Fintype.ofFinite O
    ∀ sec : O → G, (∀ a, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec a) = a) →
      Z n q col ψ = ((2 : ℂ) ^ (N * n ^ (q - 1)))⁻¹ *
        ∑ x : G → Fin N → ZMod 2, complexSign (∑ a : O,
          Algebra.trace (ZMod 2) (IntermediateField.adjoin (ZMod 2)
            (Set.range (fun i : Fin (q - 1) => ζ ^ (sec a i).val)))
            (orbitPhase ζ hζ.pow_eq_one A (displacement n col) x (sec a))) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  dsimp only
  intro sec hsec
  rw [actual_graph_replica_phase n A col ψ U c hU hform hnorm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact phase_orbit_traces hn ho ζ hζ A (displacement n col) x sec hsec

/-- The literal contraction reindexed by the full independent actual orbit-field coordinates. -/
theorem actual_graph_replica_independent_sum {N q : ℕ} (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) (ho : Odd n) (hq : 2 ≤ q)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hform : ψ = c • (tensorOp U *ᵥ graphAmp A))
    (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin (q - 1) → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    letI : Fintype O := Fintype.ofFinite O
    ∀ sec : O → G, (∀ a, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec a) = a) →
      let K := fun a : O => IntermediateField.adjoin (ZMod 2)
        (Set.range (fun i : Fin (q - 1) => ζ ^ (sec a i).val))
      letI : ∀ a : O, Fintype (K a) := fun a => Fintype.ofFinite (K a)
      letI : Fintype ((a : O) → Fin N → K a) := Fintype.ofFinite _
      ∃ e : (G → Fin N → ZMod 2) ≃ ((a : O) → Fin N → K a),
        (∀ x a u, (e x a u : F) =
          fourier ζ hζ.pow_eq_one (fun r => algebraMap (ZMod 2) F (x r u)) (sec a)) ∧
        Z n q col ψ = ((2 : ℂ) ^ (N * n ^ (q - 1)))⁻¹ *
          ∑ Y : (a : O) → Fin N → K a, complexSign (∑ a : O,
            Algebra.trace (ZMod 2) (K a)
              (orbitPhase ζ hζ.pow_eq_one A (displacement n col) (e.symm Y) (sec a))) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let G := Fin (q - 1) → ZMod n
  let p : Equiv.Perm G := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
  let O := Quotient (Equiv.Perm.SameCycle.setoid p)
  letI : Fintype O := Fintype.ofFinite O
  dsimp only
  intro sec hsec
  let K := fun a : O => IntermediateField.adjoin (ZMod 2)
    (Set.range (fun i : Fin (q - 1) => ζ ^ (sec a i).val))
  letI : ∀ a : O, Fintype (K a) := fun a => Fintype.ofFinite (K a)
  letI : Fintype ((a : O) → Fin N → K a) := Fintype.ofFinite _
  obtain ⟨e₀, he₀⟩ :=
    D5.S3.Fourier.RepresentativeOrbitCoordinates.representative_fourier_coordinates
      n (q - 1) hn ho (by omega) F ζ hζ sec hsec
  let e : (G → Fin N → ZMod 2) ≃ ((a : O) → Fin N → K a) := {
    toFun := fun x a u => e₀ (fun r => x r u) a
    invFun := fun Y r u => e₀.symm (fun a => Y a u) r
    left_inv := by
      intro x
      funext r u
      exact congrFun (e₀.symm_apply_apply (fun r => x r u)) r
    right_inv := by
      intro Y
      funext a u
      exact congrFun (e₀.apply_symm_apply (fun a => Y a u)) a }
  refine ⟨e, ?_, ?_⟩
  · intro x a u
    change (e₀ (fun r => x r u) a : F) = _
    rw [he₀]
    unfold fourier
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    change (∏ j : Fin (q - 1), ζ ^ (sec a j * r j).val) =
      AddChar.zmodChar n hζ.pow_eq_one (∑ j, sec a j * r j)
    exact (congrArg Additive.toMul
      (map_sum (AddChar.zmodChar n hζ.pow_eq_one).toAddMonoidHom _ Finset.univ)
        |>.trans (toMul_sum _ _)).symm
  · rw [actual_graph_replica_orbit_sum n hn ho F ζ hζ A col ψ U c hU hform hnorm sec hsec]
    congr 1
    let f (Y : (a : O) → Fin N → K a) := complexSign (∑ a : O,
      Algebra.trace (ZMod 2) (K a)
        (orbitPhase ζ hζ.pow_eq_one A (displacement n col) (e.symm Y) (sec a)))
    calc
      _ = ∑ x : G → Fin N → ZMod 2, f (e x) := by
        simp only [f, e.symm_apply_apply, K]
        congr 1
      _ = _ := Equiv.sum_comp e f

/-- An actual character value as an element of its generated character field. -/
def orbitCharacter (ζ : F) (hζ : ζ ^ n = 1) (t r : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val)) :=
  ⟨character ζ hζ t r, character_mem ζ hζ t r⟩

/-- The binary Fourier coefficient in the actual generated character field. -/
def orbitFourier (ζ : F) (hζ : ζ ^ n = 1) (t : Fin d → ZMod n)
    (a : (Fin d → ZMod n) → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val)) := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact ∑ r, algebraMap (ZMod 2) K (a r) * orbitCharacter ζ hζ t r

private theorem orbitFourier_coe (ζ : F) (hζ : ζ ^ n = 1) (t : Fin d → ZMod n)
    (a : (Fin d → ZMod n) → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    (orbitFourier ζ hζ t a : F) =
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) t := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  simp only [orbitFourier, IntermediateField.coe_sum, IntermediateField.coe_mul, fourier]
  apply Finset.sum_congr rfl
  intro r _
  rfl

/-- Each actual nonzero self-paired mode has its own involution and positive trace-sum factor. -/
theorem actual_self_paired_mode_count {N : ℕ} (hn : 3 ≤ n) (ho : Odd n) [Finite F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (δ : Fin N → (Fin d → ZMod n)) (t : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
    letI : Fintype K := Fintype.ofFinite K
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let lam := fun u => orbitCharacter ζ hζ.pow_eq_one t (δ u)
    let M : Matrix (Fin N) (Fin N) F := fun u v =>
      algebraMap (ZMod 2) F (A u v) *
        (character ζ hζ.pow_eq_one t (δ u) + character ζ hζ.pow_eq_one t (δ v))
    ∀ j : ℕ, (p : G → G)^[j] t = -t → t ≠ 0 →
      ∃ σ : K ≃+* K, Function.Involutive σ ∧ σ ≠ RingEquiv.refl K ∧
        Even (minimalPeriod (p : G → G) t) ∧
        (∀ a : G → Fin N → ZMod 2,
          orbitPhase ζ hζ.pow_eq_one A δ a t =
            D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A lam
              (fun u => orbitFourier ζ hζ.pow_eq_one t (fun r => a r u))
              (fun u => σ (orbitFourier ζ hζ.pow_eq_one t (fun r => a r u)))) ∧
        (∑ x : Fin N → K, complexSign (Algebra.trace (ZMod 2) K
          (D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A lam x
            (fun u => σ (x u))))) =
          (Nat.card K : ℂ) ^ (N - M.rank) *
            (Nat.card (NikolovSegal.UnitaryField.fixedField σ) : ℂ) ^ M.rank := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  letI : Fintype K := Fintype.ofFinite K
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let lam := fun u => orbitCharacter ζ hζ.pow_eq_one t (δ u)
  dsimp only
  intro j hj ht
  obtain ⟨σ, hinv, hne, heven, hgen⟩ :=
    D5.S3.Fourier.CharacterOrbitField.self_paired_character_involution
      n d hn ho F ζ hζ t j hj ht
  let g (i : Fin d) : K := ⟨ζ ^ (t i).val,
    IntermediateField.subset_adjoin (ZMod 2) _ ⟨i, rfl⟩⟩
  have hg (i : Fin d) : σ (g i) = (g i)⁻¹ := Subtype.ext (hgen i)
  have hc (r : Fin d → ZMod n) : orbitCharacter ζ hζ.pow_eq_one t r =
      ∏ i : Fin d, (g i)^(r i).val := by
    apply Subtype.ext
    simpa only [IntermediateField.coe_prod, IntermediateField.coe_pow, g, orbitCharacter]
      using character_product ζ hζ.pow_eq_one t r
  have hσlam (u : Fin N) : σ (lam u) = (lam u)⁻¹ := by
    change σ (orbitCharacter ζ hζ.pow_eq_one t (δ u)) =
      (orbitCharacter ζ hζ.pow_eq_one t (δ u))⁻¹
    rw [hc, map_prod]
    simp only [map_pow, hg, inv_pow, ← Finset.prod_inv_distrib]
  have hlam (u : Fin N) : lam u ≠ 0 := by
    intro h
    have hz := congrArg (fun z : K => (z : F)) h
    exact ((character ζ hζ.pow_eq_one t).val_isUnit (δ u)).ne_zero hz
  let η : AddChar (ZMod 2) ℂ := {
    toFun := complexSign
    map_zero_eq_one' := by simp [complexSign]
    map_add_eq_mul' := complexSign_add }
  have hη : η ≠ 1 := by
    intro h
    have hh := DFunLike.congr_fun h (1 : ZMod 2)
    change complexSign 1 = 1 at hh
    norm_num [complexSign] at hh
  have hsign (a : ZMod 2) : η a = complexSign a := rfl
  have hrank :
      (D5.S3.QuadraticForms.FiniteHermitianCharacterSum.modeMatrix A lam).rank =
        Matrix.rank (fun u v : Fin N => algebraMap (ZMod 2) F (A u v) *
          (character ζ hζ.pow_eq_one t (δ u) + character ζ hζ.pow_eq_one t (δ v))) := by
    rw [← D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap
      (L := F)]
    rfl
  have hχσ (r : Fin d → ZMod n) :
      (σ (orbitCharacter ζ hζ.pow_eq_one t r) : F) = character ζ hζ.pow_eq_one (-t) r := by
    have he : σ (orbitCharacter ζ hζ.pow_eq_one t r) =
        (orbitCharacter ζ hζ.pow_eq_one t r)⁻¹ := by
      rw [hc, map_prod]
      simp only [map_pow, hg, inv_pow, ← Finset.prod_inv_distrib]
    have he' := congrArg (fun z : K => (z : F)) he
    change _ = (character ζ hζ.pow_eq_one t r)⁻¹ at he'
    rw [character_neg, AddChar.map_neg_eq_inv]
    exact he'
  have hhatσ (a : (Fin d → ZMod n) → ZMod 2) :
      (σ (orbitFourier ζ hζ.pow_eq_one t a) : F) =
        fourier ζ hζ.pow_eq_one (fun r => algebraMap (ZMod 2) F (a r)) (-t) := by
    have hbase (b : ZMod 2) :
        (σ (algebraMap (ZMod 2) K b) : F) = algebraMap (ZMod 2) F b := by
      obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective b
      simp only [map_natCast]
      rfl
    simp only [orbitFourier, map_sum, map_mul, IntermediateField.coe_sum,
      IntermediateField.coe_mul, fourier, hχσ]
    apply Finset.sum_congr rfl
    intro r _
    rw [hbase]
  refine ⟨σ, hinv, hne, heven, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    simp only [orbitPhase, D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase,
      IntermediateField.coe_sum, apply_ite, IntermediateField.coe_zero,
      IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_one,
      IntermediateField.coe_div]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs
    · rw [orbitFourier_coe, hhatσ]
      change algebraMap (ZMod 2) F (A u v) *
        (1 + character ζ hζ.pow_eq_one t (δ v - δ u)) * _ * _ =
          _ * (1 + character ζ hζ.pow_eq_one t (δ v) /
            character ζ hζ.pow_eq_one t (δ u)) * _ * _
      rw [AddChar.map_sub_eq_div]
      rfl
    · rfl
  · have hsum := D5.S3.QuadraticForms.FiniteHermitianCharacterSum.self_paired_trace_graph_sum
      σ hinv hne N A hA lam hlam hσlam η hη
    simpa only [hsign, hrank] using hsum

/-- The actual negative Fourier coefficient inside the same generated character field. -/
def oppositeOrbitFourier (ζ : F) (hζ : ζ ^ n = 1) (t : Fin d → ZMod n)
    (a : (Fin d → ZMod n) → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val)) := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact ∑ r, algebraMap (ZMod 2) K (a r) * (orbitCharacter ζ hζ t r)⁻¹

private theorem oppositeOrbitFourier_coe (ζ : F) (hζ : ζ ^ n = 1) (t : Fin d → ZMod n)
    (a : (Fin d → ZMod n) → ZMod 2) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    (oppositeOrbitFourier ζ hζ t a : F) =
      fourier ζ hζ (fun r => algebraMap (ZMod 2) F (a r)) (-t) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  simp only [oppositeOrbitFourier, IntermediateField.coe_sum, IntermediateField.coe_mul,
    IntermediateField.coe_inv, fourier, character_neg, AddChar.map_neg_eq_inv]
  rfl

/-- Independent opposite-mode vectors have the exact orbit-degree rank factor. -/
theorem actual_paired_mode_count {N : ℕ} (hn : 3 ≤ n) (ho : Odd n) [Finite F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (δ : Fin N → (Fin d → ZMod n)) (t : Fin d → ZMod n) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
    letI : Fintype K := Fintype.ofFinite K
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let lam := fun u => orbitCharacter ζ hζ.pow_eq_one t (δ u)
    let M : Matrix (Fin N) (Fin N) F := fun u v =>
      algebraMap (ZMod 2) F (A u v) *
        (character ζ hζ.pow_eq_one t (δ u) + character ζ hζ.pow_eq_one t (δ v))
    (∀ a : G → Fin N → ZMod 2,
      phaseComponent ζ hζ.pow_eq_one A δ a t +
        phaseComponent ζ hζ.pow_eq_one A δ a (-t) =
      ((D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A lam
          (fun u => orbitFourier ζ hζ.pow_eq_one t (fun r => a r u))
          (fun u => oppositeOrbitFourier ζ hζ.pow_eq_one t (fun r => a r u)) +
        D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A
          (fun u => (lam u)⁻¹)
          (fun u => oppositeOrbitFourier ζ hζ.pow_eq_one t (fun r => a r u))
          (fun u => orbitFourier ζ hζ.pow_eq_one t (fun r => a r u))) : F)) ∧
    (∑ y : Fin N → K, ∑ x : Fin N → K,
      complexSign (Algebra.trace (ZMod 2) K
        (D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A lam x y +
          D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A
            (fun u => (lam u)⁻¹) y x))) =
      (2 : ℂ) ^ (minimalPeriod (p : G → G) t * (2 * N - M.rank)) := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
  letI : Fintype K := Fintype.ofFinite K
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let lam := fun u => orbitCharacter ζ hζ.pow_eq_one t (δ u)
  have hlam (u : Fin N) : lam u ≠ 0 := by
    intro h
    have hz := congrArg (fun z : K => (z : F)) h
    exact ((character ζ hζ.pow_eq_one t).val_isUnit (δ u)).ne_zero hz
  let η : AddChar (ZMod 2) ℂ := {
    toFun := complexSign
    map_zero_eq_one' := by simp [complexSign]
    map_add_eq_mul' := complexSign_add }
  have hη : η ≠ 1 := by
    intro h
    have hh := DFunLike.congr_fun h (1 : ZMod 2)
    change complexSign 1 = 1 at hh
    norm_num [complexSign] at hh
  let ψ := LanglandsFirstMainLemma.traceAddChar (ZMod 2) K η
  have hψ : ψ ≠ 1 :=
    (LanglandsFirstMainLemma.traceAddChar_ne_one_iff (ZMod 2) K η).mpr hη
  have hc := D5.S3.QuadraticForms.FiniteHermitianCharacterSum.paired_graph_character_sum
    A hA lam hlam ψ hψ
  have hrank :
      (D5.S3.QuadraticForms.FiniteHermitianCharacterSum.modeMatrix A lam).rank =
        Matrix.rank (fun u v : Fin N => algebraMap (ZMod 2) F (A u v) *
          (character ζ hζ.pow_eq_one t (δ u) + character ζ hζ.pow_eq_one t (δ v))) := by
    rw [← D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap
      (L := F)]
    rfl
  have hd := D5.S3.Fourier.CharacterOrbitField.character_orbit_degree n d hn ho F ζ hζ t
  have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  dsimp only
  constructor
  · intro a
    have hc₁ : phaseComponent ζ hζ.pow_eq_one A δ a t =
        ((D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A lam
          (fun u => orbitFourier ζ hζ.pow_eq_one t (fun r => a r u))
          (fun u => oppositeOrbitFourier ζ hζ.pow_eq_one t (fun r => a r u)) : K) : F) := by
      simp only [phaseComponent, D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase,
        IntermediateField.coe_sum, apply_ite, IntermediateField.coe_zero,
        IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_one,
        IntermediateField.coe_div, orbitFourier_coe, oppositeOrbitFourier_coe]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      split_ifs
      · rw [AddChar.map_sub_eq_div]
        rfl
      · rfl
    have hc₂ : phaseComponent ζ hζ.pow_eq_one A δ a (-t) =
        ((D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase A (fun u => (lam u)⁻¹)
          (fun u => oppositeOrbitFourier ζ hζ.pow_eq_one t (fun r => a r u))
          (fun u => orbitFourier ζ hζ.pow_eq_one t (fun r => a r u)) : K) : F) := by
      simp only [phaseComponent, D5.S3.QuadraticForms.FiniteHermitianCharacterSum.halfPhase,
        IntermediateField.coe_sum, apply_ite, IntermediateField.coe_zero,
        IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_one,
        IntermediateField.coe_div, IntermediateField.coe_inv, orbitFourier_coe,
        oppositeOrbitFourier_coe, neg_neg]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      split_ifs
      · rw [character_neg, AddChar.map_neg_eq_inv, AddChar.map_sub_eq_div, inv_div, inv_div_inv]
        rfl
      · rfl
    simpa only [IntermediateField.coe_add] using congrArg₂ (fun x y : F => x + y) hc₁ hc₂
  · change (∑ y : Fin N → K, ∑ x : Fin N → K, ψ _) = _
    rw [hc, hrank, hcard, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    rw [hd]


end Fourier

end
end D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
