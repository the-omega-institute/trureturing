/- GID: D5/S1/Dynamics/Shadowing/LanguageCharacterization
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LanguageCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Anchored language coloring characterizes neighborhood N-shadowing on subshifts. -/

import D5.S1.Dynamics.Shadowing.LacunaryProgressionSubshift

/-! A language characterization for Question 5.5 of Meddaugh and Stephens,
*Shadowing with small diameter sets of bounded cardinality*, arXiv:2509.04312v1. -/

open Set Function Filter SymbolicDynamics.FullShift
open scoped Uniformity

namespace D5.S1.Dynamics.Shadowing.LanguageCharacterization

variable {A : Type*}

section

variable [TopologicalSpace A]

/-- A word with coordinates in the finite integer interval `[a,b]`. -/
abbrev IntervalWord (A : Type*) (a b : ℤ) := Set.Icc a b → A

/-- Occurring words indexed by a prescribed interval. Shift invariance makes occurrence
at this interval equivalent to occurrence at any translate. -/
def intervalLanguage (X : Subshift A ℤ) (a b : ℤ) : Set (IntervalWord A a b) :=
  Set.range fun x : X.carrier => fun j => x.1 j.1

/-- Forward shift on the actual subtype of the two-sided subshift. -/
def shiftOne (X : Subshift A ℤ) (x : X.carrier) : X.carrier :=
  ⟨shift 1 x.1, X.mapsTo 1 x.2⟩

private theorem shiftOne_iterate (X : Subshift A ℤ) (x : X.carrier) (i : ℕ) (j : ℤ) :
    ((shiftOne X)^[i] x).1 j = x.1 ((i : ℤ) + j) := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', show (↑(i + 1) : ℤ) + j = (i : ℤ) + (1 + j) by omega]
    exact ih (1 + j)

/-- The position of a centered coordinate in the word on `[-m,n+m]`. -/
def centeredIndex {k m n : ℕ} (hkm : k ≤ m) (i : Set.Icc (0 : ℕ) n)
    (j : Set.Icc (-(k : ℤ)) (k : ℤ)) : Set.Icc (-(m : ℤ)) ((n : ℤ) + m) :=
  ⟨(i.1 : ℤ) + j.1, by
    have hi := i.2.2
    have ⟨hj₁, hj₂⟩ := j.2
    exact ⟨by omega, by omega⟩⟩

/-- Every centered block of radius `m` through time `n` belongs to the language. -/
def LocallyAdmissible (X : Subshift A ℤ) (m n : ℕ)
    (w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m)) : Prop :=
  ∀ i : Set.Icc (0 : ℕ) n,
    (fun j => w (centeredIndex le_rfl i j)) ∈ intervalLanguage X (-(m : ℤ)) m

/-- One language word realizes the initial block and every selected positive-time block. -/
def AnchoredExtendible (X : Subshift A ℤ) (k m n : ℕ) (hkm : k ≤ m)
    (w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m)) (S : Set (Set.Icc (1 : ℕ) n)) : Prop :=
  ∃ u ∈ intervalLanguage X (-(k : ℤ)) ((n : ℤ) + k),
    (∀ j : Set.Icc (-(k : ℤ)) (k : ℤ),
      u (centeredIndex le_rfl ⟨0, by simp⟩ j) =
        w (centeredIndex hkm ⟨0, by simp⟩ j)) ∧
    ∀ i ∈ S, ∀ j : Set.Icc (-(k : ℤ)) (k : ℤ),
      u (centeredIndex le_rfl ⟨i.1, Nat.zero_le _, i.2.2⟩ j) =
        w (centeredIndex hkm ⟨i.1, Nat.zero_le _, i.2.2⟩ j)

/-- Each color class must be jointly extendible with the same initial block. -/
def AnchoredColoring (X : Subshift A ℤ) (N k m n : ℕ) (hkm : k ≤ m)
    (w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m)) : Prop :=
  ∃ color : Set.Icc (1 : ℕ) n → Fin N,
    ∀ c, AnchoredExtendible X k m n hkm w {i | color i = c}

/-- The hyperedges are the inclusion-minimal sets of times that cannot extend with the anchor. -/
def IsForbiddenEdge (X : Subshift A ℤ) (k m n : ℕ) (hkm : k ≤ m)
    (w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m)) (s : Finset (Set.Icc (1 : ℕ) n)) :
    Prop :=
  Minimal (fun t : Finset (Set.Icc (1 : ℕ) n) => ¬ AnchoredExtendible X k m n hkm w ↑t) s

/-- A coloring extends on each class exactly when no forbidden edge is monochromatic. -/
theorem anchoredColoring_iff_no_monochromatic_edge (X : Subshift A ℤ) (N k m n : ℕ)
    (hkm : k ≤ m) (w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m)) :
    AnchoredColoring X N k m n hkm w ↔
      ∃ color : Set.Icc (1 : ℕ) n → Fin N,
        ∀ c s, IsForbiddenEdge X k m n hkm w s → ¬ ∀ i ∈ s, color i = c := by
  classical
  constructor
  · rintro ⟨color, hcolor⟩
    refine ⟨color, fun c s hs hmono => ?_⟩
    obtain ⟨u, hu, hAnchor, hClass⟩ := hcolor c
    exact hs.prop ⟨u, hu, hAnchor, fun i hi => hClass i (hmono i hi)⟩
  · rintro ⟨color, hcolor⟩
    refine ⟨color, fun c => ?_⟩
    let : Finite (Set.Icc (1 : ℕ) n) := (Set.finite_Icc 1 n).to_subtype
    let C : Set (Set.Icc (1 : ℕ) n) := {i | color i = c}
    let t := C.toFinite.toFinset
    have ht : (↑t : Set (Set.Icc (1 : ℕ) n)) = C := C.toFinite.coe_toFinset
    change AnchoredExtendible X k m n hkm w C
    by_contra hC
    have hBad : ¬ AnchoredExtendible X k m n hkm w ↑t := ht ▸ hC
    obtain ⟨s, hst, hs⟩ := exists_minimal_le_of_wellFoundedLT
      (fun u : Finset (Set.Icc (1 : ℕ) n) => ¬ AnchoredExtendible X k m n hkm w ↑u) t hBad
    apply hcolor c s hs
    intro i hi
    have hit : i ∈ (↑t : Set (Set.Icc (1 : ℕ) n)) := hst hi
    rwa [ht] at hit

/-- The local test radius is fixed before the length and the word are chosen. -/
def HasLanguageColoring (X : Subshift A ℤ) (N : ℕ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∃ hkm : k ≤ m, ∀ n : ℕ,
    ∀ w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m),
      LocallyAdmissible X m n w → AnchoredColoring X N k m n hkm w

private def Agrees (k : ℕ) (x y : ℤ → A) : Prop :=
  ∀ j ∈ Set.Icc (-(k : ℤ)) (k : ℤ), x j = y j

private def WindowShadowing (X : Subshift A ℤ) (N : ℕ) : Prop :=
  ∀ k, ∃ r, ∀ z : ℕ → X.carrier,
    (∀ i, Agrees r (shiftOne X (z i)).1 (z (i + 1)).1) →
    ∃ b : Fin N → X.carrier,
      (∀ c, Agrees k (b c).1 (z 0).1) ∧
      ∀ i, ∃ c, Agrees k ((shiftOne X)^[i] (b c)).1 (z i).1

private theorem languageColoring_of_windowShadowing {X : Subshift A ℤ} {N : ℕ}
    (h : WindowShadowing X N) : HasLanguageColoring X N := by
  classical
  intro k
  obtain ⟨r, hTrace⟩ := h k
  let m := max k (r + 1)
  have hkm : k ≤ m := le_max_left _ _
  have hrm : r + 1 ≤ m := le_max_right _ _
  refine ⟨m, hkm, ?_⟩
  intro n w hw
  have hReal (i : Set.Icc (0 : ℕ) n) :
      ∃ x : X.carrier, ∀ j : Set.Icc (-(m : ℤ)) (m : ℤ),
        x.1 j.1 = w (centeredIndex le_rfl i j) := by
    obtain ⟨x, hx⟩ := hw i
    exact ⟨x, congrFun hx⟩
  choose x hx using hReal
  let last : Set.Icc (0 : ℕ) n := ⟨n, Nat.zero_le _, le_rfl⟩
  let z (i : ℕ) : X.carrier :=
    if hi : i ≤ n then x ⟨i, Nat.zero_le _, hi⟩ else (shiftOne X)^[i - n] (x last)
  have hz (i : Set.Icc (0 : ℕ) n) : z i.1 = x i := dite_eq_left i.2.2
  have hError (i : ℕ) : Agrees r (shiftOne X (z i)).1 (z (i + 1)).1 := by
    by_cases hi : i < n
    · intro j ⟨hj₁, hj₂⟩
      rw [hz (⟨i, Nat.zero_le _, by omega⟩ : Set.Icc (0 : ℕ) n),
        hz (⟨i + 1, Nat.zero_le _, by omega⟩ : Set.Icc (0 : ℕ) n)]
      change (x _).1 (1 + j) = (x _).1 j
      rw [hx _ ⟨1 + j, by exact ⟨by omega, by omega⟩⟩,
        hx _ ⟨j, by exact ⟨by omega, by omega⟩⟩]
      congr 1
      apply Subtype.ext
      change (i : ℤ) + (1 + j) = (↑(i + 1) : ℤ) + j
      omega
    · have htail (t : ℕ) (ht : n ≤ t) : z t = (shiftOne X)^[t - n] (x last) := by
        by_cases htn : t = n
        · subst t
          simp [z, last]
        · exact dite_eq_right (by omega)
      have hstep : i + 1 - n = i - n + 1 := by omega
      rw [htail i (by omega), htail (i + 1) (by omega), hstep, iterate_succ_apply']
      exact fun _ _ => rfl
  obtain ⟨b, hb₀, hb⟩ := hTrace z hError
  choose color hcolor using fun i : Set.Icc (1 : ℕ) n => hb i.1
  have hRead (i : Set.Icc (0 : ℕ) n) (j : Set.Icc (-(k : ℤ)) (k : ℤ)) :
      (z i.1).1 j.1 = w (centeredIndex hkm i j) := by
    rw [hz i]
    have ⟨hj₁, hj₂⟩ := j.2
    exact hx i ⟨j.1, by exact ⟨by omega, by omega⟩⟩
  refine ⟨color, fun c => ⟨fun j => (b c).1 j.1, ⟨b c, rfl⟩, ?_, ?_⟩⟩
  · intro j
    have hj := hb₀ c j.1 j.2
    simpa only [centeredIndex, Nat.cast_zero, zero_add] using
      hj.trans (hRead ⟨0, by simp⟩ j)
  · intro i hi j
    have hj := hcolor i j.1 j.2
    rw [hi, shiftOne_iterate] at hj
    exact hj.trans (hRead ⟨i.1, Nat.zero_le _, i.2.2⟩ j)

private theorem windowShadowing_of_languageColoring [DiscreteTopology A] [Finite A]
    {X : Subshift A ℤ} {N : ℕ} (hN : 0 < N) (h : HasLanguageColoring X N) :
    WindowShadowing X N := by
  classical
  intro k
  obtain ⟨m, hkm, hColor⟩ := h k
  refine ⟨m, ?_⟩
  intro z hz
  have hOverlap (i : ℕ) (j : ℤ) (hj₁ : -(m : ℤ) ≤ j) (hj₂ : j ≤ m) :
      (z i).1 (j + 1) = (z (i + 1)).1 j := by
    simpa only [shiftOne, shift_apply, add_comm (1 : ℤ)] using hz i j ⟨hj₁, hj₂⟩
  let glued := signedDiagonal (fun i => (z i).1)
  have hGlued (i : ℕ) (j : ℤ) (hj : j ∈ Set.Icc (-(m : ℤ)) (m : ℤ)) :
      glued ((i : ℤ) + j) = (z i).1 j := by
    simpa [glued, pastExtension] using
      signed_diagonal_overlap hOverlap (i : ℤ) j hj.1 hj.2
  let admissible (n : ℕ) : Set (Fin N → X.carrier) := {b |
    (∀ c, Agrees k (b c).1 (z 0).1) ∧
    ∀ i : Set.Icc (0 : ℕ) n, ∃ c, Agrees k ((shiftOne X)^[i.1] (b c)).1 (z i.1).1}
  have hNonempty (n : ℕ) : (admissible n).Nonempty := by
    let w : IntervalWord A (-(m : ℤ)) ((n : ℤ) + m) := fun j => glued j.1
    have hw : LocallyAdmissible X m n w :=
      fun i => ⟨z i.1, funext fun j => (hGlued i.1 j.1 j.2).symm⟩
    obtain ⟨color, hWitness⟩ := hColor n w hw
    have hPoint (c : Fin N) :
        ∃ b : X.carrier, Agrees k b.1 (z 0).1 ∧
          ∀ i : Set.Icc (1 : ℕ) n, color i = c →
            Agrees k ((shiftOne X)^[i.1] b).1 (z i.1).1 := by
      obtain ⟨_, ⟨b, rfl⟩, hAnchor, hClass⟩ := hWitness c
      have hwindow (j : ℤ) (hj : j ∈ Set.Icc (-(k : ℤ)) (k : ℤ)) :
          j ∈ Set.Icc (-(m : ℤ)) (m : ℤ) := ⟨by have := hj.1; omega, by have := hj.2; omega⟩
      refine ⟨b, ?_, ?_⟩
      · intro j hj
        have hEq : b.1 j = glued j := by simpa [centeredIndex, w] using hAnchor ⟨j, hj⟩
        exact hEq.trans (by simpa using hGlued 0 j (hwindow j hj))
      · intro i hi j hj
        rw [shiftOne_iterate]
        exact (hClass i hi ⟨j, hj⟩).trans (hGlued i.1 j (hwindow j hj))
    choose b hAnchor hClass using hPoint
    refine ⟨b, hAnchor, ?_⟩
    intro i
    by_cases hi : i.1 = 0
    · exact ⟨⟨0, hN⟩, by simpa [hi] using hAnchor ⟨0, hN⟩⟩
    · let t : Set.Icc (1 : ℕ) n := ⟨i.1, by omega, i.2.2⟩
      exact ⟨color t, hClass (color t) t rfl⟩
  have hClosedWindow (i : ℕ) (c : Fin N) :
      IsClosed {b : Fin N → X.carrier |
        Agrees k ((shiftOne X)^[i] (b c)).1 (z i).1} := by
    simp only [Agrees, shiftOne_iterate, Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun _ => ?_
    have hEval : Continuous (fun b : Fin N → X.carrier => (b c).1 ((i : ℤ) + j)) :=
      (continuous_apply _).comp (continuous_subtype_val.comp (continuous_apply c))
    exact (isClosed_discrete ({(z i).1 j} : Set A)).preimage hEval
  have hClosed (n : ℕ) : IsClosed (admissible n) := by
    simp only [admissible, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
    apply IsClosed.inter
    · exact isClosed_iInter fun c => by simpa using hClosedWindow 0 c
    · exact isClosed_iInter fun i => isClosed_iUnion_of_finite (hClosedWindow i.1)
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  have hNested (n : ℕ) : admissible (n + 1) ⊆ admissible n :=
    fun _ hb => ⟨hb.1, fun i => hb.2 ⟨i.1, i.2.1, i.2.2.trans (Nat.le_succ _)⟩⟩
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    admissible hNested hNonempty (hClosed 0).isCompact hClosed
  have hAll : ∀ n, b ∈ admissible n := Set.mem_iInter.mp hb
  exact ⟨b, (hAll 0).1, fun i => (hAll i).2 ⟨i, Nat.zero_le _, le_rfl⟩⟩

end

private theorem agrees_entourage_basis [UniformSpace A] [DiscreteUniformity A]
    (X : Subshift A ℤ) (E : Set (X.carrier × X.carrier)) :
    E ∈ 𝓤 X.carrier ↔
      ∃ k : ℕ, ∀ x y : X.carrier, Agrees k x.1 y.1 → (x, y) ∈ E := by
  let W (j : ℤ) : Set ((ℤ → A) × (ℤ → A)) := {xy | xy.1 j = xy.2 j}
  have hU : 𝓤 (ℤ → A) = ⨅ j : ℤ, 𝓟 (W j) := by
    rw [Pi.uniformity]
    simp_rw [DiscreteUniformity.eq_principal_setRelId, Filter.comap_principal]
    rfl
  constructor
  · intro hE
    rw [uniformity_setCoe] at hE
    obtain ⟨S, hS, hSE⟩ := Filter.mem_comap.mp hE
    rw [hU] at hS
    obtain ⟨J, hJ, hJS⟩ := (hasBasis_iInf_principal_finite W).mem_iff.mp hS
    obtain ⟨k, hk⟩ := finite_integer_window hJ
    refine ⟨k, fun x y hxy => hSE (hJS ?_)⟩
    exact Set.mem_iInter₂.mpr fun j hj => hxy j (hk j hj)
  · rintro ⟨k, hk⟩
    have hW (j : ℤ) : W j ∈ 𝓤 (ℤ → A) :=
      (Pi.uniformContinuous_proj (fun _ : ℤ => A) j)
        (DiscreteUniformity.relId_mem_uniformity A)
    have hJ := (Filter.biInter_mem (Set.finite_Icc (-(k : ℤ)) k)).mpr
      (fun j _ => hW j)
    rw [uniformity_setCoe]
    refine Filter.mem_comap.mpr ⟨_, hJ, ?_⟩
    rintro ⟨x, y⟩ hxy
    exact hk x y fun j hj => Set.mem_iInter₂.mp hxy j hj

variable [TopologicalSpace A]

private theorem metric_window_controls [DiscreteTopology A] [Finite A]
    (X : Subshift A ℤ) (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier)) :
    let := d
    (∀ k : ℕ, ∃ ε > 0, ∀ x y : X.carrier,
      dist x y < ε → Agrees k x.1 y.1) ∧
    (∀ ε > 0, ∃ k : ℕ, ∀ x y : X.carrier,
      Agrees k x.1 y.1 → dist x y < ε) := by
  let : UniformSpace A :=
    (⊥ : UniformSpace A).replaceTopology
      ((inferInstance : DiscreteTopology A).eq_bot.trans UniformSpace.toTopologicalSpace_bot.symm)
  let U : UniformSpace X.carrier := inferInstance
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  have hCompact : @CompactSpace X.carrier d.toUniformSpace.toTopologicalSpace := by
    rw [hd]
    infer_instance
  have hFilter : @uniformity X.carrier d.toUniformSpace = @uniformity X.carrier U := by
    rw [← @nhdsSet_diagonal_eq_uniformity _ d.toUniformSpace hCompact,
      ← @nhdsSet_diagonal_eq_uniformity _ U inferInstance]
    have hTop : d.toUniformSpace.toTopologicalSpace = U.toTopologicalSpace := hd
    exact congrArg (fun t : TopologicalSpace X.carrier =>
      @nhdsSet _ (@instTopologicalSpaceProd _ _ t t) (diagonal X.carrier)) hTop
  let := d
  constructor
  · intro k
    let E : Set (X.carrier × X.carrier) := {xy | Agrees k xy.1.1 xy.2.1}
    have hE : E ∈ @uniformity X.carrier d.toUniformSpace := by
      rw [hFilter]
      exact (agrees_entourage_basis X E).mpr ⟨k, fun _ _ h => h⟩
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hE
    exact ⟨ε, hε, fun _ _ h => hsub h⟩
  · intro ε hε
    let E : Set (X.carrier × X.carrier) := {xy | dist xy.1 xy.2 < ε}
    have hE : E ∈ @uniformity X.carrier d.toUniformSpace := Metric.dist_mem_uniformity hε
    rw [hFilter] at hE
    exact (agrees_entourage_basis X E).mp hE

private theorem metric_iff_windowShadowing [DiscreteTopology A] [Finite A]
    (X : Subshift A ℤ) (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier))
    (N : ℕ) (hN : 0 < N) :
    let := d
    NeighborhoodFiniteShadowing N (shiftOne X) ↔ WindowShadowing X N := by
  classical
  have controls := metric_window_controls X d hd
  let := d
  obtain ⟨hSmall, hLarge⟩ := controls
  constructor
  · intro h k
    obtain ⟨ε, hε, hεk⟩ := hSmall k
    obtain ⟨δ, hδ, hTrace⟩ := h ε hε
    obtain ⟨r, hr⟩ := hLarge δ hδ
    refine ⟨r, fun z hz => ?_⟩
    obtain ⟨s, hs, hcard, hdiam, hClose⟩ := hTrace z (fun i => hr _ _ (hz i))
    have ⟨default, hdefault⟩ := hs
    let tracer (c : Fin N) : s :=
      if hc : c.1 < s.card then s.equivFin.symm ⟨c.1, hc⟩ else ⟨default, hdefault⟩
    have hSurj : Surjective tracer := by
      intro a
      let j := s.equivFin a
      refine ⟨⟨j.1, j.2.trans_le hcard⟩, ?_⟩
      simpa only [tracer, dite_eq_left j.2] using s.equivFin.symm_apply_apply a
    have hAt (i : ℕ) : ∃ a : s, Agrees k ((shiftOne X)^[i] a.1).1 (z i).1 := by
      obtain ⟨_, ⟨a, ha, rfl⟩, hdist⟩ :=
        (Metric.infDist_lt_iff (hs.to_set.image _)).mp (hClose i)
      exact ⟨⟨a, ha⟩, hεk _ _ (by simpa only [dist_comm] using hdist)⟩
    obtain ⟨a₀, ha₀⟩ := hAt 0
    refine ⟨fun c => (tracer c).1, ?_, ?_⟩
    · intro c j hj
      have hPair := Metric.dist_le_diam_of_mem s.finite_toSet.isBounded
        (tracer c).2 a₀.2
      exact (hεk _ _ (hPair.trans_lt hdiam) j hj).trans (ha₀ j hj)
    · intro i
      obtain ⟨a, ha⟩ := hAt i
      obtain ⟨c, rfl⟩ := hSurj a
      exact ⟨c, ha⟩
  · intro h ε hε
    obtain ⟨k, hk⟩ := hLarge (ε / 2) (by positivity)
    obtain ⟨r, hTrace⟩ := h k
    obtain ⟨δ, hδ, hδr⟩ := hSmall r
    refine ⟨δ, hδ, fun z hz => ?_⟩
    obtain ⟨b, hb₀, hb⟩ := hTrace z (fun i => hδr _ _ (hz i))
    let s := Finset.univ.image b
    have hs : s.Nonempty := ⟨b ⟨0, hN⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
    refine ⟨s, hs, Finset.card_image_le.trans_eq (by simp), ?_, ?_⟩
    · refine (Metric.diam_le_of_forall_dist_le_of_nonempty hs.to_set ?_).trans_lt
        (show ε / 2 < ε by linarith)
      intro x hx y hy
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨c', _, rfl⟩ := Finset.mem_image.mp hy
      exact (hk _ _ (fun j hj => (hb₀ c j hj).trans (hb₀ c' j hj).symm)).le
    · intro i
      obtain ⟨c, hc⟩ := hb i
      apply (Metric.infDist_lt_iff (hs.to_set.image _)).mpr
      refine ⟨(shiftOne X)^[i] (b c), ⟨b c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
        rfl⟩, ?_⟩
      rw [dist_comm]
      exact (hk _ _ hc).trans (by linarith)

/-- Meddaugh–Stephens neighborhood `N`-shadowing is equivalent to finite anchored
language coloring for every positive finite `N` and every compatible metric. -/
theorem neighborhoodFiniteShadowing_iff_languageColoring [DiscreteTopology A] [Finite A]
    (X : Subshift A ℤ) (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier))
    (N : ℕ) (hN : 0 < N) :
    let := d
    NeighborhoodFiniteShadowing N (shiftOne X) ↔ HasLanguageColoring X N := by
  have h := metric_iff_windowShadowing X d hd N hN
  exact h.trans ⟨languageColoring_of_windowShadowing, windowShadowing_of_languageColoring hN⟩

#print axioms neighborhoodFiniteShadowing_iff_languageColoring
#print axioms anchoredColoring_iff_no_monochromatic_edge

end D5.S1.Dynamics.Shadowing.LanguageCharacterization
