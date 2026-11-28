/- GID: D5/S3/Combinatorics/Matroids/QTransversalDirectSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/QTransversalDirectSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The concatenated presentation gives the rank of the direct sum of q-transversal q-matroids. -/

import D5.S3.Combinatorics.Matroids.QTransversalRepresentability

/-!
Fulcher, *Cyclic Flats of a q-Matroid*, arXiv:2603.13550v1, Conjecture 4.8:
https://arxiv.org/html/2603.13550v1#S4.Thmtheorem8.
The direct sum uses Definition 2.7 and the presentations use Definition 2.12.
-/

namespace D5.S3.Combinatorics.Matroids.QTransversalRepresentability

open Module Submodule

variable {F : Type} [Field F] [Fintype F] {m n k ℓ : ℕ}

open Classical in
private noncomputable def slotCount (X : Fin k → Submodule F (Fin m → F))
    (T : Submodule F (Fin m → F)) : ℕ :=
  (Finset.univ.filter fun i => ¬ T ≤ X i).card

open Classical in
omit [Fintype F] in
private lemma count_add_containing (X : Fin k → Submodule F (Fin m → F))
    (T : Submodule F (Fin m → F)) :
    (Finset.univ.filter fun i => T ≤ X i).card + slotCount X T = k := by
  classical
  simpa only [slotCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => T ≤ X i))

omit [Fintype F] in
private lemma count_mono (X : Fin k → Submodule F (Fin m → F))
    {S T : Submodule F (Fin m → F)} (hST : S ≤ T) : slotCount X S ≤ slotCount X T := by
  classical
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, fun h => hi.2 (hST.trans h)⟩

private noncomputable def presentationCost (X : Fin k → Submodule F (Fin m → F))
    (U T : Submodule F (Fin m → F)) : ℕ :=
  slotCount X T + (finrank F U - finrank F T)

private theorem presentation_rank_eq_minimum (X : Fin k → Submodule F (Fin m → F))
    (U : Submodule F (Fin m → F)) :
    qTransversalRank X U =
      sInf {d | ∃ T ≤ U, d = slotCount X T + (finrank F U - finrank F T)} := by
  classical
  change qTransversalRank X U = sInf {d | ∃ T ≤ U, d = presentationCost X U T}
  rw [presentation_rank_eq_hallMinimum]
  let hallCost (J : Finset (Fin k)) :=
    (finrank F U - finrank F ↥(U ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1)) + (k - J.card)
  change sInf (Set.range hallCost) = _
  apply le_antisymm
  · have hm : ∃ T ≤ U, sInf {d | ∃ T ≤ U, d = presentationCost X U T} =
        presentationCost X U T := Nat.sInf_mem (s := {d | ∃ T ≤ U, d = presentationCost X U T})
          ⟨presentationCost X U U, U, le_rfl, rfl⟩
    obtain ⟨T, hTU, hT⟩ := hm
    rw [hT]
    let J := Finset.univ.filter fun i => T ≤ X i
    refine (Nat.sInf_le (s := Set.range (hallCost)) ⟨J, rfl⟩).trans ?_
    have ht : T ≤ U ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1 :=
      le_inf hTU (le_iInf fun i => (Finset.mem_filter.mp i.2).2)
    have hd := Submodule.finrank_mono ht
    have hj : J.card + slotCount X T = k := count_add_containing X T
    unfold hallCost presentationCost
    omega
  · have hm : ∃ J, hallCost J = sInf (Set.range (hallCost)) :=
      Nat.sInf_mem (s := Set.range (hallCost)) ⟨hallCost ∅, ∅, rfl⟩
    obtain ⟨J, hJ⟩ := hm
    rw [← hJ]
    let C : Submodule F (Fin m → F) := U ⊓ ⨅ i : {i : Fin k // i ∈ J}, X i.1
    refine (Nat.sInf_le (s := {d | ∃ T ≤ U, d = presentationCost X U T})
      ⟨C, inf_le_left, rfl⟩).trans ?_
    have hsubset : J ⊆ Finset.univ.filter (fun i => C ≤ X i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, inf_le_right.trans
        (iInf_le (fun j : {j : Fin k // j ∈ J} => X j.1) ⟨i, hi⟩)⟩
    have hcard := Finset.card_le_card hsubset
    have hc := count_add_containing X C
    change slotCount X C + (finrank F U - finrank F C) ≤
      (finrank F U - finrank F C) + (k - J.card)
    omega

/-- The coordinate isomorphism with the external direct sum. -/
def splitCoordinates : (Fin (m + n) → F) ≃ₗ[F] (Fin m → F) × (Fin n → F) :=
  (LinearEquiv.piCongrLeft' F (fun _ : Fin (m + n) => F) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) F F)

def firstProjection : (Fin (m + n) → F) →ₗ[F] (Fin m → F) :=
  (LinearMap.fst F _ _).comp splitCoordinates.toLinearMap

def secondProjection : (Fin (m + n) → F) →ₗ[F] (Fin n → F) :=
  (LinearMap.snd F _ _).comp splitCoordinates.toLinearMap

def concatenatedPresentation (X : Fin k → Submodule F (Fin m → F))
    (Y : Fin ℓ → Submodule F (Fin n → F)) :
    Fin (k + ℓ) → Submodule F (Fin (m + n) → F) :=
  Fin.append (fun i => (X i).comap firstProjection) (fun j => (Y j).comap secondProjection)

omit [Fintype F] in
private lemma count_concat (X : Fin k → Submodule F (Fin m → F))
    (Y : Fin ℓ → Submodule F (Fin n → F)) (W : Submodule F (Fin (m + n) → F)) :
    slotCount (concatenatedPresentation X Y) W =
      slotCount X (W.map firstProjection) + slotCount Y (W.map secondProjection) := by
  classical
  simp only [slotCount, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp only [concatenatedPresentation, Fin.append_left, Fin.append_right,
    Submodule.map_le_iff_le_comap]

omit [Fintype F] in
private lemma preimage_finrank {V V' : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (p : V →ₗ[F] V') (W : Submodule F V) (A : Submodule F V') (hA : A ≤ W.map p) :
    finrank F ↥(W ⊓ A.comap p) + finrank F ↥(W.map p) = finrank F W + finrank F A := by
  have hd := ((A.mkQ.comp p).domRestrict W).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, LinearMap.ker_comp,
    A.ker_mkQ, ← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype,
    Submodule.map_comp] at hd
  have hq := LinearRado.quotient_sum_finrank A (W.map p)
  rw [sup_eq_left.mpr hA] at hq
  omega

omit [Fintype F] in
private lemma joint_preimage {V V₁ V₂ : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
    [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₂]
    (p : V →ₗ[F] V₁) (q : V →ₗ[F] V₂) (W : Submodule F V)
    (A : Submodule F V₁) (B : Submodule F V₂) (hA : A ≤ W.map p) (hB : B ≤ W.map q) :
    ∃ T ≤ W, T.map p ≤ A ∧ T.map q ≤ B ∧
      finrank F W - finrank F T ≤
        (finrank F ↥(W.map p) - finrank F A) + (finrank F ↥(W.map q) - finrank F B) := by
  let S := W ⊓ A.comap p
  let R := W ⊓ B.comap q
  let T := S ⊓ R
  have hSW : S ≤ W := inf_le_left
  have hRW : R ≤ W := inf_le_left
  have hTS : T ≤ S := inf_le_left
  have hTR : T ≤ R := inf_le_right
  have hTW := hTS.trans hSW
  have hSA : S ≤ A.comap p := inf_le_right
  have hRB : R ≤ B.comap q := inf_le_right
  refine ⟨T, hTW, Submodule.map_le_iff_le_comap.mpr (hTS.trans hSA),
    Submodule.map_le_iff_le_comap.mpr (hTR.trans hRB), ?_⟩
  have hS : finrank F S + finrank F ↥(W.map p) = finrank F W + finrank F A :=
    preimage_finrank p W A hA
  have hR : finrank F R + finrank F ↥(W.map q) = finrank F W + finrank F B :=
    preimage_finrank q W B hB
  have hT := Submodule.finrank_sup_add_finrank_inf_eq S R
  have hSup := Submodule.finrank_mono (sup_le hSW hRW)
  have hTdim := Submodule.finrank_mono hTW
  have hAdim := Submodule.finrank_mono hA
  have hBdim := Submodule.finrank_mono hB
  change finrank F W - finrank F ↥(S ⊓ R) ≤ _
  omega

private lemma presentation_minimum_attained (X : Fin k → Submodule F (Fin m → F))
    (U : Submodule F (Fin m → F)) :
    ∃ T ≤ U, qTransversalRank X U = presentationCost X U T := by
  rw [presentation_rank_eq_minimum]
  exact Nat.sInf_mem (s := {d | ∃ T ≤ U, d = presentationCost X U T})
    ⟨presentationCost X U U, U, le_rfl, rfl⟩

private lemma rank_le_presentationCost (X : Fin k → Submodule F (Fin m → F))
    {U T : Submodule F (Fin m → F)} (hTU : T ≤ U) :
    qTransversalRank X U ≤ presentationCost X U T := by
  rw [presentation_rank_eq_minimum]
  exact Nat.sInf_le ⟨T, hTU, rfl⟩

private noncomputable def directSumCost (X : Fin k → Submodule F (Fin m → F))
    (Y : Fin ℓ → Submodule F (Fin n → F)) (U W : Submodule F (Fin (m + n) → F)) : ℕ :=
  qTransversalRank X (W.map firstProjection) +
    qTransversalRank Y (W.map secondProjection) + (finrank F U - finrank F W)

set_option maxHeartbeats 600000 in
theorem fulcher_conjecture_4_8 (X : Fin k → Submodule F (Fin m → F))
    (Y : Fin ℓ → Submodule F (Fin n → F)) (U : Submodule F (Fin (m + n) → F)) :
    qTransversalRank (concatenatedPresentation X Y) U =
      sInf {d | ∃ W ≤ U, d = qTransversalRank X (W.map firstProjection) +
        qTransversalRank Y (W.map secondProjection) + (finrank F U - finrank F W)} := by
  classical
  let costs : Set ℕ := {d | ∃ W ≤ U, d = directSumCost X Y U W}
  have hCosts : costs.Nonempty := ⟨directSumCost X Y U U, U, le_rfl, rfl⟩
  apply le_antisymm
  · obtain ⟨W, hWU, hW⟩ := Nat.sInf_mem hCosts
    let p : (Fin (m + n) → F) →ₗ[F] (Fin m → F) := firstProjection
    let q : (Fin (m + n) → F) →ₗ[F] (Fin n → F) := secondProjection
    obtain ⟨A, hAP, hA⟩ := presentation_minimum_attained X (W.map p)
    obtain ⟨B, hBQ, hB⟩ := presentation_minimum_attained Y (W.map q)
    obtain ⟨T, hTW, hTA, hTB, hcodim⟩ := joint_preimage p q W A B hAP hBQ
    have hcount : slotCount (concatenatedPresentation X Y) T ≤ slotCount X A + slotCount Y B :=
      (count_concat X Y T).le.trans (Nat.add_le_add (count_mono X hTA) (count_mono Y hTB))
    have hWdim := Submodule.finrank_mono hWU
    have hTdim := Submodule.finrank_mono hTW
    calc
      qTransversalRank (concatenatedPresentation X Y) U ≤
          presentationCost (concatenatedPresentation X Y) U T :=
        rank_le_presentationCost _ (hTW.trans hWU)
      _ ≤ presentationCost X (W.map p) A + presentationCost Y (W.map q) B +
          (finrank F U - finrank F W) := by
        unfold presentationCost
        omega
      _ = directSumCost X Y U W :=
        congrArg (fun d => d + (finrank F U - finrank F W))
          (congrArg₂ Nat.add hA.symm hB.symm)
      _ = sInf costs := hW.symm
  · obtain ⟨T, hTU, hT⟩ := presentation_minimum_attained (concatenatedPresentation X Y) U
    have hp : qTransversalRank X (T.map firstProjection) ≤ slotCount X (T.map firstProjection) := by
      simpa only [presentationCost, Nat.sub_self, Nat.add_zero] using
        rank_le_presentationCost X (le_refl (T.map firstProjection))
    have hq : qTransversalRank Y (T.map secondProjection) ≤ slotCount Y (T.map secondProjection) := by
      simpa only [presentationCost, Nat.sub_self, Nat.add_zero] using
        rank_le_presentationCost Y (le_refl (T.map secondProjection))
    calc
      sInf costs ≤ directSumCost X Y U T := Nat.sInf_le (s := costs) ⟨T, hTU, rfl⟩
      _ ≤ slotCount X (T.map firstProjection) + slotCount Y (T.map secondProjection) +
          (finrank F U - finrank F T) := Nat.add_le_add_right (Nat.add_le_add hp hq) _
      _ = presentationCost (concatenatedPresentation X Y) U T :=
        congrArg (fun d => d + (finrank F U - finrank F T)) (count_concat X Y T).symm
      _ = qTransversalRank (concatenatedPresentation X Y) U := hT.symm

end D5.S3.Combinatorics.Matroids.QTransversalRepresentability
