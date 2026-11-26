/- GID: D5/S3/Combinatorics/Lattices/EuclideanHNEquivariance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/EuclideanHNEquivariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral isometries preserve saturated sublattices and every Euclidean HN stage. -/

import D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan

/-! Integral isometries act on saturated sublattices through their actual ambient images.
Gram determinants give covariance of the degree, and HN uniqueness fixes every stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance

open Module Matrix EuclideanSublattices EuclideanHarderNarasimhan HarderNarasimhan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
variable (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)

/-- Restriction of an ambient lattice-preserving isometry to the integral lattice. -/
def latticeEquiv : L ≃ₗ[ℤ] L := by
  let f : L →ₗ[ℤ] L :=
    { toFun := fun x => ⟨T x, hT.le (Submodule.mem_map_of_mem x.property)⟩
      map_add' := fun _ _ => Subtype.ext (T.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul (T.toLinearMap.restrictScalars ℤ) _ _) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (T.injective (congrArg Subtype.val h))
  · intro y
    have hy : (y : E) ∈ L.map (T.toLinearMap.restrictScalars ℤ) := by
      rw [hT]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private theorem latticeEquiv_symm_coe (x : L) :
    ((latticeEquiv L T hT).symm x : E) = T.symm x := by
  apply T.injective
  rw [T.apply_symm_apply]
  exact congrArg (fun y : L => (y : E)) ((latticeEquiv L T hT).apply_symm_apply x)

private theorem ambient_map (M : Submodule ℤ L) :
    ambient L (M.map (latticeEquiv L T hT).toLinearMap) =
      (ambient L M).map (T.toLinearMap.restrictScalars ℤ) := by
  rw [ambient, ambient, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

private theorem realSpan_map (M : Submodule ℤ L) :
    realSpan L (M.map (latticeEquiv L T hT).toLinearMap) =
      (realSpan L M).map T.toLinearMap := by
  rw [EuclideanSublattices.realSpan, EuclideanSublattices.realSpan, ambient_map]
  change Submodule.span ℝ (T '' (ambient L M : Set E)) = _
  exact Submodule.span_image T.toLinearMap

private theorem saturation_map (M : Submodule ℤ L) :
    saturation L (M.map (latticeEquiv L T hT).toLinearMap) =
      (saturation L M).map (latticeEquiv L T hT).toLinearMap := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (x : E) ∈ realSpan L (M.map (latticeEquiv L T hT).toLinearMap) ↔
    ((latticeEquiv L T hT).symm x : E) ∈ realSpan L M
  rw [realSpan_map, Submodule.mem_map_equiv, latticeEquiv_symm_coe]
  rfl

private theorem closed_map_iff (M : Submodule ℤ L) :
    (closure L).IsClosed (M.map (latticeEquiv L T hT).toLinearMap) ↔
      (closure L).IsClosed M := by
  rw [(closure L).isClosed_iff, (closure L).isClosed_iff]
  change saturation L (M.map (latticeEquiv L T hT).toLinearMap) =
    M.map (latticeEquiv L T hT).toLinearMap ↔ saturation L M = M
  rw [saturation_map]
  exact (Submodule.orderIsoMapComap (latticeEquiv L T hT)).injective.eq_iff

/-- The actual image of a saturated sublattice under the restricted ambient isometry. -/
def sublatticeMap (M : Sublattice L) : Sublattice L :=
  ⟨M.val.map (latticeEquiv L T hT).toLinearMap,
    (closed_map_iff L T hT M.val).mpr M.property⟩

/-- The order automorphism of saturated sublattices induced by the ambient isometry. -/
def sublatticeEquiv : Sublattice L ≃o Sublattice L where
  toFun := sublatticeMap L T hT
  invFun M := ⟨(Submodule.orderIsoMapComap (latticeEquiv L T hT)).symm M.val, by
    apply (closed_map_iff L T hT _).mp
    change (closure L).IsClosed
      ((Submodule.orderIsoMapComap (latticeEquiv L T hT))
        ((Submodule.orderIsoMapComap (latticeEquiv L T hT)).symm M.val))
    rw [OrderIso.apply_symm_apply]
    exact M.property⟩
  left_inv M := Subtype.ext ((Submodule.orderIsoMapComap (latticeEquiv L T hT)).left_inv M.val)
  right_inv M := Subtype.ext ((Submodule.orderIsoMapComap (latticeEquiv L T hT)).right_inv M.val)
  map_rel_iff' := (Submodule.orderIsoMapComap (latticeEquiv L T hT)).map_rel_iff

private theorem integral_map (M : Sublattice L) :
    integral L (sublatticeEquiv L T hT M) =
      (integral L M).map (T.toLinearMap.restrictScalars ℤ) := ambient_map L T hT M.val

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- The actual Gram determinant of a chosen integral basis of the ambient carrier. -/
def gramDet (A : Sublattice L) : ℝ :=
  (Matrix.gram ℝ (fun i => (Module.Free.chooseBasis ℤ (integral L A) i : E))).det

private theorem rank_preserved (M : Sublattice L) :
    (slopeData L).rank (sublatticeEquiv L T hT M) = (slopeData L).rank M := by
  change (Module.finrank ℤ (M.val.map (latticeEquiv L T hT).toLinearMap) : ℤ) = _
  exact congrArg (fun n : ℕ => (n : ℤ))
    (Submodule.equivMapOfInjective (latticeEquiv L T hT).toLinearMap
      (latticeEquiv L T hT).injective M.val).finrank_eq.symm

private theorem covolume_preserved (M : Sublattice L) :
    covolume (integral L (sublatticeEquiv L T hT M)) = covolume (integral L M) := by
  classical
  let A := integral L M
  let B := integral L (sublatticeEquiv L T hT M)
  let e₀ := Submodule.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective A
  let e : A ≃ₗ[ℤ] B := e₀.trans (LinearEquiv.ofEq _ _ (integral_map L T hT M).symm)
  let b := Module.Free.chooseBasis ℤ A
  have he (x : A) : (e x : E) = T x := rfl
  rw [covolume_eq_gram B (b.map e), covolume_eq_gram A b]
  congr 2
  ext i j
  simp only [gram_apply, Basis.map_apply, he, T.inner_map_map]

private theorem slope_preserved (A B : Sublattice L) :
    (slopeData L).slope (sublatticeEquiv L T hT A) (sublatticeEquiv L T hT B) =
      (slopeData L).slope A B := by
  simp only [SlopeData.slope, rank_preserved]
  change (-Real.log (covolume (integral L (sublatticeEquiv L T hT B))) -
    -Real.log (covolume (integral L (sublatticeEquiv L T hT A)))) / _ = _
  rw [covolume_preserved, covolume_preserved]
  rfl

private theorem semistable_map {A B : Sublattice L}
    (h : (slopeData L).Semistable A B) :
    (slopeData L).Semistable (sublatticeEquiv L T hT A) (sublatticeEquiv L T hT B) := by
  let e := sublatticeEquiv L T hT
  refine ⟨e.strictMono h.1, ?_⟩
  intro X hAX hXB
  obtain ⟨Y, rfl⟩ := e.surjective X
  rw [slope_preserved, slope_preserved]
  exact h.2 Y (e.lt_iff_lt.mp hAX) (e.le_iff_le.mp hXB)

private theorem filtration_map {A B : Sublattice L} {l : List (Sublattice L)}
    (h : (slopeData L).Filtration A B l) :
    (slopeData L).Filtration (sublatticeEquiv L T hT A) (sublatticeEquiv L T hT B)
      (l.map (sublatticeEquiv L T hT)) := by
  induction h with
  | nil a => exact .nil _
  | @cons a e b l hs heb tail drop ih =>
    apply SlopeData.Filtration.cons (semistable_map L T hT hs)
      ((sublatticeEquiv L T hT).monotone heb) ih
    cases l with
    | nil => trivial
    | cons c l =>
      change (slopeData L).slope _ _ < _
      rw [slope_preserved, slope_preserved]
      exact drop

/-- The endpoint after the consecutive HN factors of slope strictly greater than t. -/
def above (D : SlopeData (Sublattice L)) (t : ℝ) :
    Sublattice L → List (Sublattice L) → Sublattice L
  | a, [] => a
  | a, b :: l => if t < D.slope a b then above D t b l else a

private theorem above_fixed (l : List (Sublattice L))
    (hl : ∀ A ∈ l, sublatticeEquiv L T hT A = A)
    (a : Sublattice L) (ha : sublatticeEquiv L T hT a = a) (t : ℝ) :
    sublatticeEquiv L T hT (above L (slopeData L) t a l) =
      above L (slopeData L) t a l := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    simp only [above]
    split
    · exact ih (fun A hA => hl A (List.mem_cons_of_mem _ hA)) b
        (hl b (List.mem_cons_self ..))
    · exact ha

/-- Every lattice-preserving linear isometry preserves the actual ranks and Gram covolumes,
transports HN filtrations, and fixes every stage and every strict slope truncation. -/
theorem isometry_hn :
    let Λ := Sublattice L
    let e : Λ → Λ := sublatticeMap L T hT
    let D : SlopeData Λ := slopeData L
    let R : Λ → ℤ := D.rank
    let F : Λ → Λ → List Λ → Prop := D.Filtration
    let C : Λ → ℝ := fun A => covolume (integral L A)
    let G : Λ → ℝ := gramDet L
    let H : ℝ → Λ → List Λ → Λ := above L D
    (∀ A : Λ, R (e A) = R A ∧ C (e A) = Real.sqrt (G A)) ∧
    (∀ (A B : Λ) (l : List Λ), F A B l ↔ F (e A) (e B) (l.map e)) ∧
    ∀ (A B : Λ) (l : List Λ), e A = A → e B = B → F A B l →
      l.map e = l ∧ (∀ K ∈ l, e K = K) ∧
      ∀ t : ℝ, e (H t A l) = H t A l := by
  dsimp only
  refine ⟨fun A => ⟨rank_preserved L T hT A, covolume_preserved L T hT A⟩,
    ?_, ?_⟩
  · intro A B l
    refine ⟨filtration_map L T hT, ?_⟩
    intro hl
    have endpoints_le {X Y : Sublattice L} {k : List (Sublattice L)}
        (hk : (slopeData L).Filtration X Y k) : X ≤ Y := by
      cases hk with
      | nil => exact le_rfl
      | cons hs hb _ _ => exact hs.1.le.trans hb
    have hAB : A ≤ B := by
      exact (sublatticeEquiv L T hT).le_iff_le.mp (endpoints_le hl)
    obtain ⟨k, hk, _⟩ := ((euclidean_hn L A B).2.1).mpr hAB
    obtain ⟨_, _, hu⟩ := ((euclidean_hn L
      (sublatticeEquiv L T hT A) (sublatticeEquiv L T hT B)).2.1).mpr
        ((sublatticeEquiv L T hT).monotone hAB)
    have hm : k.map (sublatticeEquiv L T hT) = l.map (sublatticeEquiv L T hT) :=
      (hu _ (filtration_map L T hT hk)).trans (hu _ hl).symm
    have hkl : k = l := List.map_injective_iff.mpr
      (sublatticeEquiv L T hT).injective hm
    exact hkl ▸ hk
  · intro A B l hA hB hl
    have hAB : A ≤ B := by
      cases hl with
      | nil => exact le_rfl
      | cons hs hb _ _ => exact hs.1.le.trans hb
    obtain ⟨k, hk, hu⟩ := ((euclidean_hn L A B).2.1).mpr hAB
    have hm := filtration_map L T hT hl
    change sublatticeEquiv L T hT A = A at hA
    change sublatticeEquiv L T hT B = B at hB
    rw [hA, hB] at hm
    have he : l.map (sublatticeEquiv L T hT) = l := (hu _ hm).trans (hu _ hl).symm
    have hf : ∀ F ∈ l, sublatticeEquiv L T hT F = F := by
      clear hk hu hl hm k hAB
      induction l with
      | nil => simp
      | cons a l ih =>
        have hc := List.cons.inj he
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hc.1
        · exact ih hc.2 b hb
    exact ⟨he, hf, fun t => above_fixed L T hT l hf A hA t⟩

end D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance
