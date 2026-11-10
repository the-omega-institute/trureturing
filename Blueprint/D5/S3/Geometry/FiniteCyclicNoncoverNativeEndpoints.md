# FiniteCyclicNoncoverNativeEndpoints

## Abstract

Actual original cyclic native sequences expose cell boundaries, ordered pair coverage, all frames/counts, and full-endpoint coordinate equations.

Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.

**Theorem 1.1 (native_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem native_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    let A := criticalData_zero q hq s

    let K := noncover (show 0 < 3*q by omega) s

    let X := X_zero q hq s

    let C := C_zero q hq s

    let S := main_zero q hq s

    let T := core_zero q hq s

    let PS := mainPairs_zero q hq s

    let PT := corePairs_zero q hq s

    let H := mainSDR_zero q hq s

    let G := coreSDR_zero q hq s

    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧

    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧

    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧

    (∀ a ∈ X, a.card ≤ 2*q-1) ∧

    (A.critical.card = 2) ∧

    (S.pairs.map CollapsePair.lower).Nodup ∧

    (T.pairs.map CollapsePair.lower).Nodup ∧

    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PS) ∧

    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PT) ∧

    (∀ e ∈ (matching (by omega) s).pairs,

      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧

      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧

    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,

      a ∈ S.frames.getD i X ↔ a ∈ K ∧

        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,

      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧

        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧

    (S.frames.getD PS.length X = X ∧

      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧

    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧

    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧

      (faceSet C).card = 1 + 2*PT.length) ∧

    ((faceSet X).card = (faceSet C).card + 2 ∧

      (faceSet K).card = 1 + 2 + 2*(PS.length+PT.length)) ∧

    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,

      (H.homotopy (t, x)).val v = x.val v) ∧

    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,

      (G.homotopy (t, x)).val v = x.val v) ∧

    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧

      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧

    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧

      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧

    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧

    (∀ y : Space (vertexComplex A.p), ∀ v : V,

      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧

    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧

    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)

**Theorem 1.2 (native_one).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem native_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    let A := criticalData_one q hq s

    let K := noncover (show 0 < 3*q+1 by omega) s

    let X := X_one q hq s

    let C := C_one q hq s

    let S := main_one q hq s

    let T := core_one q hq s

    let PS := mainPairs_one q hq s

    let PT := corePairs_one q hq s

    let H := mainSDR_one q hq s

    let G := coreSDR_one q hq s

    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧

    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧

    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧

    (∀ a ∈ X, a.card ≤ 2*q) ∧

    (A.critical.card = 1) ∧

    (S.pairs.map CollapsePair.lower).Nodup ∧

    (T.pairs.map CollapsePair.lower).Nodup ∧

    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PS) ∧

    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PT) ∧

    (∀ e ∈ (matching (by omega) s).pairs,

      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧

      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧

    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,

      a ∈ S.frames.getD i X ↔ a ∈ K ∧

        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,

      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧

        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧

    (S.frames.getD PS.length X = X ∧

      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧

    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧

    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧

      (faceSet C).card = 1 + 2*PT.length) ∧

    ((faceSet X).card = (faceSet C).card + 1 ∧

      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧

    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,

      (H.homotopy (t, x)).val v = x.val v) ∧

    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,

      (G.homotopy (t, x)).val v = x.val v) ∧

    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧

      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧

    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧

      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧

    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧

    (∀ y : Space (vertexComplex A.p), ∀ v : V,

      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧

    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧

    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)

**Theorem 1.3 (native_two).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem native_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    let A := criticalData_two q hq s

    let K := noncover (show 0 < 3*q+2 by omega) s

    let X := X_two q hq s

    let C := C_two q hq s

    let S := main_two q hq s

    let T := core_two q hq s

    let PS := mainPairs_two q hq s

    let PT := corePairs_two q hq s

    let H := mainSDR_two q hq s

    let G := coreSDR_two q hq s

    (∀ a : Finset V, a ∈ X ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧

    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧

    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧

    (∀ a ∈ X, a.card ≤ 2*q) ∧

    (A.critical.card = 1) ∧

    (S.pairs.map CollapsePair.lower).Nodup ∧

    (T.pairs.map CollapsePair.lower).Nodup ∧

    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PS) ∧

    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧

      (P.lower, P.upper) ∈ PT) ∧

    (∀ e ∈ (matching (by omega) s).pairs,

      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧

      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧

    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,

      a ∈ S.frames.getD i X ↔ a ∈ K ∧

        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,

      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧

        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧

    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧

    (S.frames.getD PS.length X = X ∧

      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧

    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧

    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧

      (faceSet C).card = 1 + 2*PT.length) ∧

    ((faceSet X).card = (faceSet C).card + 1 ∧

      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧

    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,

      (H.homotopy (t, x)).val v = x.val v) ∧

    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,

      (G.homotopy (t, x)).val v = x.val v) ∧

    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧

      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧

    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧

      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧

    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧

    (∀ y : Space (vertexComplex A.p), ∀ v : V,

      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧

    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧

    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_one`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_two`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverNativeEndpoints.native_zero`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverNative](FiniteCyclicNoncoverNative.md)
