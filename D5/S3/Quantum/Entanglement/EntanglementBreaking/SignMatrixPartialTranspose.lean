/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Output partial transpose preserves the Hermitian sign matrix distribution. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.SignMatrixNetBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking
open _root_.Matrix
open MeasureTheory ProbabilityTheory
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

abbrev PTIndex (d : ℕ) := Fin d × Fin d
def ptLt {d : ℕ} (i j : PTIndex d) : Prop := finProdFinEquiv i < finProdFinEquiv j
instance ptLt_decidable {d : ℕ} (i j : PTIndex d) : Decidable (ptLt i j) := by unfold ptLt; infer_instance

/-- The two product indices exchanged by second-factor partial transpose. -/
def ptCross {d : ℕ} (i j : PTIndex d) : PTIndex d × PTIndex d :=
  ((i.1, j.2), (j.1, i.2))

/-- Pull back an upper-triangular sign coordinate through partial transpose.
The imaginary bit is complemented exactly when the transported orientation reverses. -/
def ptBitTransform {d : ℕ}
    (ω : HermitianSignIndex (PTIndex d) → Bool) : HermitianSignIndex (PTIndex d) → Bool := fun idx =>
    let b := idx.1
    let i := idx.2.1
    let j := idx.2.2
    if ptLt i j then
      let r := (ptCross i j).1
      let s := (ptCross i j).2
      if ptLt r s then ω (b, (r, s))
      else if ptLt s r then if b then !(ω (true, (s, r))) else ω (false, (s, r))
      else false
    else ω idx

private theorem ptCross_cross {d : ℕ} (i j : PTIndex d) :
    ptCross (ptCross i j).1 (ptCross i j).2 = (i, j) := by
  cases i
  cases j
  rfl

private theorem ptCross_ne {d : ℕ} {i j : PTIndex d} (hij : i ≠ j) :
    (ptCross i j).1 ≠ (ptCross i j).2 := by
  intro h
  apply hij
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  cases i
  cases j
  simp_all [ptCross]

private theorem signScalar_conj (ε η : Bool) :
    starRingEnd ℂ (signScalar ε η) = signScalar ε (!η) := by
  cases ε <;> cases η <;>
    apply Complex.ext <;>
      norm_num [signScalar, Complex.star_def, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]

private theorem ptBitTransform_apply_not_lt {d : ℕ} (ω : HermitianSignIndex (PTIndex d) → Bool)
    (b : Bool) (i j : PTIndex d) (h : ¬ ptLt i j) :
    ptBitTransform ω (b, (i,j)) = ω (b,(i,j)) := by
  change (if ptLt i j then _ else ω (b,(i,j))) = _
  rw [if_neg h]

private theorem ptBitTransform_apply_lt_forward {d : ℕ} (ω : HermitianSignIndex (PTIndex d) → Bool)
    (b : Bool) (i j : PTIndex d) (hij : ptLt i j)
    (hrs : ptLt (ptCross i j).1 (ptCross i j).2) :
    ptBitTransform ω (b,(i,j)) = ω (b,((ptCross i j).1,(ptCross i j).2)) := by
  unfold ptBitTransform
  dsimp
  rw [if_pos hij, if_pos hrs]

private theorem ptBitTransform_apply_lt_reverse {d : ℕ} (ω : HermitianSignIndex (PTIndex d) → Bool)
    (b : Bool) (i j : PTIndex d) (hij : ptLt i j)
    (hrs : ¬ ptLt (ptCross i j).1 (ptCross i j).2)
    (hsr : ptLt (ptCross i j).2 (ptCross i j).1) :
    ptBitTransform ω (b,(i,j)) =
      (if b then !(ω (true,((ptCross i j).2,(ptCross i j).1)))
       else ω (false,((ptCross i j).2,(ptCross i j).1))) := by
  unfold ptBitTransform
  dsimp
  rw [if_pos hij, if_neg hrs, if_pos hsr]

private theorem ptLt_trichotomy {d : ℕ} (i j : PTIndex d) :
    ptLt i j ∨ i = j ∨ ptLt j i := by
  unfold ptLt
  rcases lt_trichotomy (finProdFinEquiv i) (finProdFinEquiv j) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (finProdFinEquiv.injective h))
  · exact Or.inr (Or.inr h)

private theorem ptBitTransform_involutive {d : ℕ} (ω : HermitianSignIndex (PTIndex d) → Bool) :
    ptBitTransform (ptBitTransform ω) = ω := by
  funext idx
  rcases idx with ⟨b, ij⟩
  rcases ij with ⟨i,j⟩
  by_cases hij : ptLt i j
  · let r := (ptCross i j).1
    let s := (ptCross i j).2
    have hijne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl (finProdFinEquiv i)) hij
    have hrs : r ≠ s := ptCross_ne hijne
    by_cases hrs' : ptLt r s
    · have hsr : ¬ ptLt s r := by intro h; exact lt_asymm hrs' h
      have hcross : ptCross r s = (i,j) := ptCross_cross i j
      rw [ptBitTransform_apply_lt_forward (ptBitTransform ω) b i j hij hrs']
      rw [ptBitTransform_apply_lt_forward ω b r s hrs' (by simpa [hcross] using hij)]
      rw [hcross]
    · have hsr : ptLt s r := by
        rcases ptLt_trichotomy r s with h | h | h
        · exact False.elim (hrs' h)
        · exact False.elim (hrs h)
        · exact h
      have hcross : ptCross s r = (j,i) := by cases i; cases j; rfl
      have hji : ¬ ptLt j i := by intro h; exact lt_asymm hij h
      rw [ptBitTransform_apply_lt_reverse (ptBitTransform ω) b i j hij hrs' hsr]
      by_cases hb : b
      · simp only [hb, ↓reduceIte]
        rw [ptBitTransform_apply_lt_reverse ω true s r hsr hji hij]
        simp [hcross]
      · simp only [hb, ↓reduceIte]
        rw [ptBitTransform_apply_lt_reverse ω false s r hsr hji hij]
        simp [hcross]
  · exact ptBitTransform_apply_not_lt (ptBitTransform ω) b i j hij |>.trans (ptBitTransform_apply_not_lt ω b i j hij)

end D5.S3.Quantum.Entanglement.EntanglementBreaking

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking
open _root_.Matrix
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

theorem partialTranspose_signCubeSample {d : ℕ}
    (ω : HermitianSignIndex (PTIndex d) → Bool) :
    partialTranspose (signCubeSample ω) = signCubeSample (ptBitTransform ω) := by
  classical
  letI : LinearOrder (PTIndex d) := Equiv.linearOrder finProdFinEquiv
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hpq : (i,j) = (k,l)
  · rcases Prod.mk.inj hpq with ⟨rfl, rfl⟩
    simp [partialTranspose, signCubeSample, finiteSignSample, finiteSignMatrix]
  · have hcross : (i,l) ≠ (k,j) := by
      intro h
      apply hpq
      cases i
      cases j
      cases k
      cases l
      simp_all
    by_cases hp : finProdFinEquiv (i,j) < finProdFinEquiv (k,l)
    · by_cases hrs : finProdFinEquiv (i,l) < finProdFinEquiv (k,j)
      · have hp' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,j) (k,l) := by exact hp
        have hrs' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,l) (k,j) := by exact hrs
        have hsrnot : ¬ finProdFinEquiv (k,j) < finProdFinEquiv (i,l) := by intro h; exact lt_asymm hrs h
        simp [partialTranspose, signCubeSample, finiteSignSample, finiteSignMatrix,
          ptBitTransform, ptLt, ptCross, signScalar_conj, hp, hrs, hp', hrs', hpq, hcross]
      · have hsr : finProdFinEquiv (k,j) < finProdFinEquiv (i,l) := by
          rcases lt_trichotomy (finProdFinEquiv (i,l)) (finProdFinEquiv (k,j)) with h | h | h
          · exact False.elim (hrs h)
          · exact False.elim (hcross (finProdFinEquiv.injective h))
          · exact h
        have hp' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,j) (k,l) := by exact hp
        have hrs' : ¬ @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,l) (k,j) := by exact hrs
        have hsr' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (k,j) (i,l) := by exact hsr
        simp [partialTranspose, signCubeSample, finiteSignSample, finiteSignMatrix,
          ptBitTransform, ptLt, ptCross, signScalar_conj, hp, hrs, hsr, hp', hrs', hsr', hpq, hcross]
    · have hqp : finProdFinEquiv (k,l) < finProdFinEquiv (i,j) := by
        rcases lt_trichotomy (finProdFinEquiv (i,j)) (finProdFinEquiv (k,l)) with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hpq (finProdFinEquiv.injective h))
        · exact h
      have hpn' : ¬ @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,j) (k,l) := by exact hp
      by_cases hrs : finProdFinEquiv (i,l) < finProdFinEquiv (k,j)
      · have hqp' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (k,l) (i,j) := by exact hqp
        have hrs' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,l) (k,j) := by exact hrs
        have hsrnot : ¬ finProdFinEquiv (k,j) < finProdFinEquiv (i,l) := by intro h; exact lt_asymm hrs h
        simp [partialTranspose, signCubeSample, finiteSignSample, finiteSignMatrix,
          ptBitTransform, ptLt, ptCross, signScalar_conj, hp, hqp, hrs, hqp', hpn', hrs', hsrnot, hpq, hcross]
      · have hsr : finProdFinEquiv (k,j) < finProdFinEquiv (i,l) := by
          rcases lt_trichotomy (finProdFinEquiv (i,l)) (finProdFinEquiv (k,j)) with h | h | h
          · exact False.elim (hrs h)
          · exact False.elim (hcross (finProdFinEquiv.injective h))
          · exact h
        have hqp' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (k,l) (i,j) := by exact hqp
        have hrs' : ¬ @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (i,l) (k,j) := by exact hrs
        have hsr' : @LT.lt _ (Equiv.linearOrder finProdFinEquiv).toLT (k,j) (i,l) := by exact hsr
        simp [partialTranspose, signCubeSample, finiteSignSample, finiteSignMatrix,
          ptBitTransform, ptLt, ptCross, signScalar_conj, hp, hqp, hrs, hsr, hqp', hpn', hrs', hsr', hpq, hcross]

end D5.S3.Quantum.Entanglement.EntanglementBreaking

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking
open _root_.Matrix
open MeasureTheory ProbabilityTheory
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

private theorem uniformSignMeasure_preimage_eq {I : Type*} [Fintype I]
    (T : (I → Bool) → (I → Bool)) (hT : Function.Bijective T) (E : Set (I → Bool)) :
    (signCubeMeasure I).real (T ⁻¹' E) = (signCubeMeasure I).real E := by
  letI : Fintype (I → Bool) := Fintype.ofFinite _
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have hmap : Measure.map T (signCubeMeasure I) = signCubeMeasure I := by
    unfold signCubeMeasure
    ext s hs
    rw [Measure.map_apply (measurable_of_countable T) hs, uniformOn_univ, uniformOn_univ,
      Measure.count_apply (hs.preimage (measurable_of_countable T)), Measure.count_apply hs]
    congr 1
    rw [Set.encard_preimage_of_bijective hT]
  calc
    (signCubeMeasure I).real (T ⁻¹' E) =
        (Measure.map T (signCubeMeasure I)).real E := by
      unfold Measure.real
      rw [Measure.map_apply (measurable_of_countable T) hE]
    _ = (signCubeMeasure I).real E := congrArg (fun ν : Measure (I → Bool) => ν.real E) hmap

private theorem ptBitTransform_bijective {d : ℕ} :
    Function.Bijective (@ptBitTransform d) := by
  constructor
  · intro a b hab
    apply_fun ptBitTransform at hab
    simpa only [ptBitTransform_involutive] using hab
  · intro a
    exact ⟨ptBitTransform a, ptBitTransform_involutive a⟩

/-- The fixed-vector quadratic tail is inherited from the original sample by the
orientation-reversing coordinate involution. -/
theorem signCubeSample_partialTranspose_quadratic_tail {d : ℕ}
    (x : Fin d × Fin d → ℂ) (hx : ‖WithLp.toLp 2 x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | t ≤ ‖star x ⬝ᵥ
        (partialTranspose (signCubeSample ω) *ᵥ x)‖} ≤
      2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ))) := by
  let T := @ptBitTransform d
  let E : Set (HermitianSignIndex (Fin d × Fin d) → Bool) :=
    {ω | t ≤ ‖star x ⬝ᵥ (signCubeSample ω *ᵥ x)‖}
  have hset : {ω | t ≤ ‖star x ⬝ᵥ
        (partialTranspose (signCubeSample ω) *ᵥ x)‖} = T ⁻¹' E := by
    ext ω
    change (t ≤ ‖star x ⬝ᵥ (partialTranspose (signCubeSample ω) *ᵥ x)‖) ↔
      (t ≤ ‖star x ⬝ᵥ (signCubeSample (T ω) *ᵥ x)‖)
    rw [partialTranspose_signCubeSample ω]
  rw [hset, uniformSignMeasure_preimage_eq T (ptBitTransform_bijective (d := d)) E]
  exact signCubeSample_quadratic_tail x hx ht

end D5.S3.Quantum.Entanglement.EntanglementBreaking
