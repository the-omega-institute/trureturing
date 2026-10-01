/- GID: D5/S3/Quantum/Measurement/VisibleAdaptiveRecordLaw
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/VisibleAdaptiveRecordLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite adaptive local instruments have hidden-state independent records and exact absolute minimax risk. -/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import D5.S3.Quantum.Divergence.DualAccountFull
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Basic
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.seminormedAddCommGroup
local instance (I : Type*) : MeasurableSpace (Matrix I I ℂ) := inferInstanceAs (MeasurableSpace (I → I → ℂ))
local instance (I : Type*) [Fintype I] : ContinuousENorm (Matrix I I ℂ) := inferInstanceAs (ContinuousENorm (I → I → ℂ))
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped CStarAlgebra MatrixOrder ComplexOrder ComplexConjugate ENNReal BigOperators
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open scoped Kronecker
set_option maxHeartbeats 800000
universe u v
namespace D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
structure ActualHistory (H : Type u) (A : Type v) [MeasurableSpace H] [Fintype A] where
  law : Measure H
  probability : IsProbabilityMeasure law
  density : H → Matrix A A ℂ
  measurable_density : Measurable density
  integrable_density : Integrable density law
  state_density : ∀ h, (density h).PosSemidef ∧ Matrix.trace (density h) = 1
structure LegalAdaptiveStage (H T : Type u) (A : Type v) [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] where
  Outcome : H → Type u
  outcomeMeasurable : ∀ h, MeasurableSpace (Outcome h)
  embed : ∀ h, Outcome h → T
  legal : ∀ h F, MeasurableSet F → @MeasurableSet (Outcome h) (outcomeMeasurable h) (embed h ⁻¹' F)
  preceding : T → H
  measurable_preceding : Measurable preceding
  preceding_embed : ∀ h o, preceding (embed h o) = h
  operation : ∀ h, Set (Outcome h) → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ)
  empty_operation : ∀ h X, CStarMatrix.ofMatrix.symm (operation h ∅ (CStarMatrix.ofMatrix X)) = 0
  additive_operation : ∀ h (f : ℕ → Set (Outcome h)), (∀ n, @MeasurableSet (Outcome h) (outcomeMeasurable h) (f n)) → Pairwise (fun m n => Disjoint (f m) (f n)) → ∀ X i j, HasSum (fun n => CStarMatrix.ofMatrix.symm (operation h (f n) (CStarMatrix.ofMatrix X)) i j) (CStarMatrix.ofMatrix.symm (operation h (⋃ n, f n) (CStarMatrix.ofMatrix X)) i j)
  trace_preserving : ∀ h X, Matrix.trace (CStarMatrix.ofMatrix.symm (operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X
  measurable_operation : ∀ F, MeasurableSet F → ∀ a b i j, Measurable (fun h => CStarMatrix.ofMatrix.symm (operation h (embed h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)
open NormedSpace
open scoped Classical
structure RawAdaptiveStage (H T : Type u) (A : Type v) [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] (stop : Set H) where
  Outcome : H → Type u
  outcomeMeasurable : ∀ h, MeasurableSpace (Outcome h)
  embed : ∀ h, Outcome h → T
  legal : ∀ h F, MeasurableSet F → @MeasurableSet (Outcome h) (outcomeMeasurable h) (embed h ⁻¹' F)
  preceding : T → H
  measurable_preceding : Measurable preceding
  preceding_embed : ∀ h o, preceding (embed h o) = h
  operation : ∀ h, Set (Outcome h) → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ)
  empty_operation : ∀ h X, CStarMatrix.ofMatrix.symm (operation h ∅ (CStarMatrix.ofMatrix X)) = 0
  additive_operation : ∀ h (f : ℕ → Set (Outcome h)), (∀ n, @MeasurableSet (Outcome h) (outcomeMeasurable h) (f n)) → Pairwise (fun m n => Disjoint (f m) (f n)) → ∀ X i j, HasSum (fun n => CStarMatrix.ofMatrix.symm (operation h (f n) (CStarMatrix.ofMatrix X)) i j) (CStarMatrix.ofMatrix.symm (operation h (⋃ n, f n) (CStarMatrix.ofMatrix X)) i j)
  trace_preserving : ∀ h, h ∉ stop → ∀ X, Matrix.trace (CStarMatrix.ofMatrix.symm (operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X
  measurable_operation : ∀ F, MeasurableSet F → ∀ a b i j, Measurable (fun h => CStarMatrix.ofMatrix.symm (operation h (embed h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)
noncomputable def actualWait {A : Type*} [Fintype A] [DecidableEq A] (H : Matrix A A ℂ) (t : ℝ) : Matrix A A ℂ := by letI : NormedRing (Matrix A A ℂ) := Matrix.instL2OpNormedRing
                                                                                                                     letI : NormedAlgebra ℂ (Matrix A A ℂ) := Matrix.instL2OpNormedAlgebra
                                                                                                                     letI : NormedAlgebra ℚ (Matrix A A ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
                                                                                                                     exact NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.DualAccountFull
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
structure RealOutput (H : Type*) [MeasurableSpace H] where
  kernel : Kernel H ℝ
  markov : IsMarkovKernel kernel
structure ActualEventStage (H T : Type u) (A : Type v) [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] where
  Outcome : H → Type u
  outcomeMeasurable : ∀ h, MeasurableSpace (Outcome h)
  embed : ∀ h, Outcome h → T
  legal : ∀ h F, MeasurableSet F → @MeasurableSet (Outcome h) (outcomeMeasurable h) (embed h ⁻¹' F)
  preceding : T → H
  measurable_preceding : Measurable preceding
  preceding_embed : ∀ h o, preceding (embed h o) = h
  operation : ∀ h, Set (Outcome h) → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ)
  empty_operation : ∀ h X, CStarMatrix.ofMatrix.symm (operation h ∅ (CStarMatrix.ofMatrix X)) = 0
  additive_operation : ∀ h (f : ℕ → Set (Outcome h)), (∀ n, @MeasurableSet (Outcome h) (outcomeMeasurable h) (f n)) → Pairwise (fun m n => Disjoint (f m) (f n)) → ∀ X i j, HasSum (fun n => CStarMatrix.ofMatrix.symm (operation h (f n) (CStarMatrix.ofMatrix X)) i j) (CStarMatrix.ofMatrix.symm (operation h (⋃ n, f n) (CStarMatrix.ofMatrix X)) i j)
  measurable_operation : ∀ F, MeasurableSet F → ∀ a b i j, Measurable (fun h => CStarMatrix.ofMatrix.symm (operation h (embed h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)
noncomputable def normalizationDomain {H T : Type u} {A : Type v} [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] (J : ActualEventStage H T A) : Set H := {h | ∀ a b, Matrix.trace (CStarMatrix.ofMatrix.symm (J.operation h Set.univ (CStarMatrix.ofMatrix (Matrix.single a b 1)))) = Matrix.trace (Matrix.single a b (1 : ℂ))}
structure StoppedPolicy (H : ℕ → Type u) (D : Type u) (A : Type) [∀ n, MeasurableSpace (H n)] [MeasurableSpace D] [Fintype A] [DecidableEq A] where
  stop : ∀ n, Set (H n)
  measurable_stop : ∀ n, MeasurableSet (stop n)
  stage : ∀ n, ActualEventStage (H n) (H (n+1)) A
  time : ∀ n, H n → ℝ
  measurable_time : ∀ n, Measurable (time n)
  cemetery : ∀ n, H n → H (n+1)
  measurable_cemetery : ∀ n, Measurable (cemetery n)
  preceding_cemetery : ∀ n h, (stage n).preceding (cemetery n h) = h
  stopped_cemetery : ∀ n h, h ∈ stop n → cemetery n h ∈ stop (n+1)
  record : ∀ n, H n → ℕ × D
  measurable_record : ∀ n, Measurable (record n)
  stopped_record : ∀ n h, h ∈ stop n → record (n+1) (cemetery n h) = record n h
  active_length : ∀ n h o, h ∉ stop n → (record (n+1) ((stage n).embed h o)).1 = (record n h).1 + 1
noncomputable def actualStoppedStep {H : ℕ → Type u} {D : Type u} {A B : Type} [∀ n, MeasurableSpace (H n)] [MeasurableSpace D] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (P : StoppedPolicy H D A) (H_A : Matrix A A ℂ) (n : ℕ) (h : H n) (E : Set (H (n+1))) (X : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ := if h ∈ P.stop n then (if P.cemetery n h ∈ E then X else 0) else
    let V := actualWait (H_A ⊗ₖ (1 : Matrix B B ℂ)) (P.time n h)
    let Φ := (P.stage n).operation h ((P.stage n).embed h ⁻¹' E)
    let f := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
    PhyslibLeaf.MatrixMap.kron f LinearMap.id (V * X * Vᴴ)
noncomputable def completedStoppedStep {H : ℕ → Type u} {D : Type u} {A B : Type} [∀ n, MeasurableSpace (H n)] [MeasurableSpace D] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (P : StoppedPolicy H D A) (H_A : Matrix A A ℂ) (n : ℕ) (h : H n) (E : Set (H (n+1))) (X : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ := if h ∈ P.stop n ∪ (normalizationDomain (P.stage n))ᶜ then (if P.cemetery n h ∈ E then X else 0) else
    let V := actualWait (H_A ⊗ₖ (1 : Matrix B B ℂ)) (P.time n h)
    let Φ := (P.stage n).operation h ((P.stage n).embed h ⁻¹' E)
    let f := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
    PhyslibLeaf.MatrixMap.kron f LinearMap.id (V * X * Vᴴ)
def historyIndex (N n : ℕ) : Fin (N+1) := ⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right n N)⟩
structure FiniteStoppedPolicy (N : ℕ) (F : Fin (N+1) → Type u) (D : Type u) (A : Type) [∀ i, MeasurableSpace (F i)] [MeasurableSpace D] [Fintype A] [DecidableEq A] where
  stop : ∀ n, n < N → Set (F (historyIndex N n))
  measurable_stop : ∀ n hn, MeasurableSet (stop n hn)
  stage : ∀ n, n < N → ActualEventStage (F (historyIndex N n)) (F (historyIndex N (n+1))) A
  time : ∀ n, n < N → F (historyIndex N n) → ℝ
  measurable_time : ∀ n hn, Measurable (time n hn)
  cemetery : ∀ n, n < N → F (historyIndex N n) → F (historyIndex N (n+1))
  measurable_cemetery : ∀ n hn, Measurable (cemetery n hn)
  preceding_cemetery : ∀ n hn h, (stage n hn).preceding (cemetery n hn h) = h
  stopped_cemetery : ∀ n hn hnnext h, h ∈ stop n hn → cemetery n hn h ∈ stop (n+1) hnnext
  record : ∀ i, F i → ℕ × D
  measurable_record : ∀ i, Measurable (record i)
  stopped_record : ∀ n hn h, h ∈ stop n hn → record (historyIndex N (n+1)) (cemetery n hn h) = record (historyIndex N n) h
  active_length : ∀ n hn h o, h ∉ stop n hn → (record (historyIndex N (n+1)) ((stage n hn).embed h o)).1 = (record (historyIndex N n) h).1 + 1
noncomputable def actualFiniteStep {N : ℕ} {F : Fin (N+1) → Type u} {D : Type u} {A B : Type} [∀ i, MeasurableSpace (F i)] [MeasurableSpace D] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (P : FiniteStoppedPolicy N F D A) (H_A : Matrix A A ℂ) (n : ℕ) (hn : n < N) (h : F (historyIndex N n)) (E : Set (F (historyIndex N (n+1)))) (X : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ := if h ∈ P.stop n hn then (if P.cemetery n hn h ∈ E then X else 0) else
    let V := actualWait (H_A ⊗ₖ (1 : Matrix B B ℂ)) (P.time n hn h)
    let Φ := (P.stage n hn).operation h ((P.stage n hn).embed h ⁻¹' E)
    let f := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
    PhyslibLeaf.MatrixMap.kron f LinearMap.id (V * X * Vᴴ)
/-- A finite measurable protocol uses only visible instruments and the actual local-Hamiltonian tensor wait. Its physical retained record law is independent of every hidden density state. On that same record, arbitrary real randomized estimators have exact extended expected absolute minimax risk log(e)/(2β). -/
theorem visible_adaptive_record_law_and_absolute_minimax {A : Type} [Fintype A] [DecidableEq A] (e : ℕ) (he : 2 ≤ e) (β : ℝ) (hβ : 0 < β) (N : ℕ) (F : Fin (N+1) → Type u) [∀ i, MeasurableSpace (F i)] (D : Type u) [MeasurableSpace D] (P : FiniteStoppedPolicy N F D A) (H_A : Matrix A A ℂ) (hH_A : H_A.IsHermitian) (h₀ : F (historyIndex N 0)) (ρ₀ : Matrix A A ℂ) (hρ₀ : ρ₀.PosSemidef) (hρ₀trace : Matrix.trace ρ₀ = 1) (G : DensityState (Fin e) → ∀ i, ActualHistory (F i) (A × Fin e)) (hinit : ∀ σ, (G σ (historyIndex N 0)).law = Measure.dirac h₀) (hproduct : ∀ σ, (G σ (historyIndex N 0)).density =ᵐ[(G σ (historyIndex N 0)).law] (fun _ => ρ₀ ⊗ₖ CStarMatrix.ofMatrix.symm σ.1)) (hnormalized : ∀ σ n hn, ∀ᵐ h ∂(G σ (historyIndex N n)).law, h ∉ P.stop n hn →
      ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm ((P.stage n hn).operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X)
    (hphysical : ∀ σ n hn E, MeasurableSet E → ∀ i j, (∫ h in E, (G σ (historyIndex N (n+1))).density h i j ∂(G σ (historyIndex N (n+1))).law) = ∫ h, actualFiniteStep P H_A n hn h E ((G σ (historyIndex N n)).density h) i j ∂(G σ (historyIndex N n)).law) :
    letI : NeZero e := ⟨by omega⟩
    let θ := fun σ : DensityState (Fin e) => (Real.log e - vonNeumannEntropy σ) / β
    ∃ μ : Measure (F (historyIndex N N)), IsProbabilityMeasure μ ∧ (∀ σ, (G σ (historyIndex N N)).law = μ) ∧ (∀ σ, (G σ (historyIndex N N)).law.map (P.record (historyIndex N N)) = μ.map (P.record (historyIndex N N))) ∧ (∀ σ n hn, ∀ E : Set (ℕ × D), MeasurableSet E → (G σ (historyIndex N (n+1))).law ((P.stage n hn).preceding ⁻¹' P.stop n hn ∩ P.record (historyIndex N (n+1)) ⁻¹' E) = (G σ (historyIndex N n)).law (P.stop n hn ∩ P.record (historyIndex N n) ⁻¹' E)) ∧ (⨅ κ : RealOutput (ℕ × D), ⨆ σ : DensityState (Fin e), ∫⁻ z : ℝ, ENNReal.ofReal |z - θ σ| ∂(((G σ (historyIndex N N)).law.map (P.record (historyIndex N N))).bind κ.kernel)) = ENNReal.ofReal (Real.log e / (2 * β)) := by
  classical
  letI : NeZero e := ⟨by omega⟩
  dsimp only
  have hpadding (N : ℕ) (F : Fin (N+1) → Type u) [mF : ∀ i, MeasurableSpace (F i)] (D : Type u) [MeasurableSpace D] (A : Type) [Fintype A] [DecidableEq A] (record : ∀ i, F i → ℕ × D) (hmrecord : ∀ i, Measurable (record i)) :
      let ix := fun n => (⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right n N)⟩ : Fin (N+1))
      let H := fun n => F (ix n)
      letI : ∀ n, MeasurableSpace (H n) := fun n => inferInstanceAs (MeasurableSpace (F (ix n)))
      ∀ (stop : ∀ n, n < N → Set (H n)) (hmstop : ∀ n hn, MeasurableSet (stop n hn)) (stage : ∀ n, n < N → ActualEventStage (H n) (H (n+1)) A) (time : ∀ n, n < N → H n → ℝ) (hmtime : ∀ n hn, Measurable (time n hn)) (cem : ∀ n, n < N → H n → H (n+1)) (hmcem : ∀ n hn, Measurable (cem n hn)) (hprev : ∀ n hn h, (stage n hn).preceding (cem n hn h) = h) (hpersist : ∀ n hn hnnext h, h ∈ stop n hn → cem n hn h ∈ stop (n+1) hnnext) (hrecord : ∀ n hn h, h ∈ stop n hn → record (ix (n+1)) (cem n hn h) = record (ix n) h) (hlength : ∀ n hn h o, h ∉ stop n hn → (record (ix (n+1)) ((stage n hn).embed h o)).1 = (record (ix n) h).1 + 1),
      ∃ P : StoppedPolicy H D A, (∀ n hn, P.stage n = stage n hn) ∧ (∀ n hn, P.stop n = stop n hn) ∧ (∀ n hn, P.time n = time n hn) ∧ (∀ n hn, P.cemetery n = cem n hn) ∧ (∀ n, P.record n = record (ix n)) := by classical
    dsimp only
    let ix := fun n => (⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right n N)⟩ : Fin (N+1))
    let H := fun n => F (ix n)
    letI : ∀ n, MeasurableSpace (H n) := fun n => inferInstanceAs (MeasurableSpace (F (ix n)))
    intro stop hmstop stage time hmtime cem hmcem hprev hpersist hrecord hlength
    let zeroCP : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ) :=
      { toLinearMap := 0
        map_cstarMatrix_nonneg' := by intro k X hX
                                      have hz : X.map (0 : CStarMatrix A A ℂ →ₗ[ℂ] CStarMatrix A A ℂ) = 0 := by ext i j
                                                                                                                rfl
                                      rw [hz] }
    let zero (T : Type u) [MeasurableSpace T] : ActualEventStage T T A :=
      { Outcome := fun _ => PEmpty
        outcomeMeasurable := fun _ => ⊤
        embed := fun _ x => nomatch x
        legal := fun _ E hE => by simp
        preceding := id
        measurable_preceding := measurable_id
        preceding_embed := fun _ o => nomatch o
        operation := fun _ _ => zeroCP
        empty_operation := fun _ X => by ext i j; rfl
        additive_operation := fun h f hf hd X i j => by change HasSum (fun _ : ℕ => (0 : ℂ)) 0
                                                        exact hasSum_zero
        measurable_operation := fun E hE a b i j => by simpa [zeroCP] using (measurable_const : Measurable (fun _ : T => (0 : ℂ))) }
    have tail (n : ℕ) (hn : ¬n < N) :
        ∃ J : ActualEventStage (H n) (H (n+1)) A,
          ∃ c : H n → H (n+1), Measurable c ∧ (∀ h, J.preceding (c h) = h) ∧ (∀ h, record (ix (n+1)) (c h) = record (ix n) h) := by
      have hi : ix (n+1) = ix n := by apply Fin.ext
                                      dsimp [ix]
                                      omega
      change ∃ J : @ActualEventStage (F (ix n)) (F (ix (n+1))) A (mF (ix n)) (mF (ix (n+1))) _ _,
        ∃ c : F (ix n) → F (ix (n+1)), @Measurable _ _ (mF (ix n)) (mF (ix (n+1))) c ∧ (∀ h, J.preceding (c h) = h) ∧ (∀ h, record (ix (n+1)) (c h) = record (ix n) h)
      rw [hi]; exact ⟨zero (F (ix n)), id, measurable_id, (fun _ => rfl), (fun _ => rfl)⟩
    let stop' (n : ℕ) : Set (H n) := if hn : n < N then stop n hn else Set.univ
    let stage' (n : ℕ) : ActualEventStage (H n) (H (n+1)) A := if hn : n < N then stage n hn else (tail n hn).choose
    let time' (n : ℕ) : H n → ℝ := if hn : n < N then time n hn else fun _ => 0
    let cem' (n : ℕ) : H n → H (n+1) := if hn : n < N then cem n hn else (tail n hn).choose_spec.choose
    let P : StoppedPolicy H D A :=
      { stop := stop'
        measurable_stop := fun n => by by_cases hn : n < N
                                       · simpa only [stop', dif_pos hn] using hmstop n hn
                                       · simp only [stop', dif_neg hn, MeasurableSet.univ]
        stage := stage'
        time := time'
        measurable_time := fun n => by by_cases hn : n < N
                                       · simpa only [time', dif_pos hn] using hmtime n hn
                                       · simpa only [time', dif_neg hn] using (measurable_const : Measurable (fun _ : H n => (0 : ℝ)))
        cemetery := cem'
        measurable_cemetery := fun n => by by_cases hn : n < N
                                           · simpa only [cem', dif_pos hn] using hmcem n hn
                                           · simpa only [cem', dif_neg hn] using (tail n hn).choose_spec.choose_spec.1
        preceding_cemetery := fun n h => by by_cases hn : n < N
                                            · simpa only [stage', cem', dif_pos hn] using hprev n hn h
                                            · simpa only [stage', cem', dif_neg hn] using (tail n hn).choose_spec.choose_spec.2.1 h
        stopped_cemetery := fun n h hs => by by_cases hn : n < N
                                             · by_cases hnnext : n+1 < N
                                               · simpa only [stop', cem', dif_pos hn, dif_pos hnnext] using hpersist n hn hnnext h (by simpa only [stop', dif_pos hn] using hs)
                                               · simp only [stop', dif_neg hnnext, Set.mem_univ]
                                             · have hnnext : ¬n+1 < N := by omega
                                               simp only [stop', dif_neg hnnext, Set.mem_univ]
        record := fun n => record (ix n)
        measurable_record := fun n => hmrecord (ix n)
        stopped_record := fun n h hs => by by_cases hn : n < N
                                           · simpa only [cem', dif_pos hn] using hrecord n hn h (by simpa only [stop', dif_pos hn] using hs)
                                           · simpa only [cem', dif_neg hn] using (tail n hn).choose_spec.choose_spec.2.2 h
        active_length := fun n h => by by_cases hn : n < N
                                       · have hl (J : ActualEventStage (H n) (H (n+1)) A) (he : J = stage n hn) :
                                             ∀ o : J.Outcome h, h ∉ stop' n → (record (ix (n+1)) (J.embed h o)).1 = (record (ix n) h).1 + 1 := by
                                           subst J
                                           intro o hs; exact hlength n hn h o (by simpa only [stop', dif_pos hn] using hs)
                                         exact hl (stage' n) (dif_pos hn)
                                       · intro o hs
                                         have : False := by simpa only [stop', dif_neg hn, Set.mem_univ, not_true_eq_false] using hs
                                         exact this.elim }
    refine ⟨P, ?_, ?_, ?_, ?_, (fun n => rfl)⟩
    · intro n hn
      simp only [P, stage', dif_pos hn]
    · intro n hn
      simp only [P, stop', dif_pos hn]
    · intro n hn
      simp only [P, time', dif_pos hn]
    · intro n hn
      simp only [P, cem', dif_pos hn]
  have hbounded {A : Type} [Fintype A] [DecidableEq A] (e : ℕ) (he : 2 ≤ e) (β : ℝ) (hβ : 0 < β) (H : ℕ → Type u) [∀ n, MeasurableSpace (H n)] (D : Type u) [MeasurableSpace D] (P : StoppedPolicy H D A) (H_A : Matrix A A ℂ) (hH_A : H_A.IsHermitian) (h₀ : H 0) (ρ₀ : Matrix A A ℂ) (hρ₀ : ρ₀.PosSemidef) (hρ₀trace : Matrix.trace ρ₀ = 1) (G : DensityState (Fin e) → ∀ n, ActualHistory (H n) (A × Fin e)) (hinit : ∀ σ, (G σ 0).law = Measure.dirac h₀) (hproduct : ∀ σ, (G σ 0).density =ᵐ[(G σ 0).law] (fun _ => ρ₀ ⊗ₖ CStarMatrix.ofMatrix.symm σ.1)) (N : ℕ) (hnormalized : ∀ σ n, n < N → ∀ᵐ h ∂(G σ n).law, h ∉ P.stop n →
        ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm ((P.stage n).operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X)
      (hphysical : ∀ σ n, n < N → ∀ E, MeasurableSet E → ∀ i j, (∫ h in E, (G σ (n+1)).density h i j ∂(G σ (n+1)).law) = ∫ h, actualStoppedStep P H_A n h E ((G σ n).density h) i j ∂(G σ n).law)
      :
      letI : NeZero e := ⟨by omega⟩
      let ω := gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)
      let θ := fun σ : DensityState (Fin e) => quantumRelativeEntropy σ ω / β
      ∃ μ : Measure (H N), IsProbabilityMeasure μ ∧ (∀ σ, (G σ N).law = μ) ∧ (∀ σ, (G σ N).law.map (P.record N) = μ.map (P.record N)) ∧ (∀ σ n, n < N → ∀ F : Set (ℕ × D), MeasurableSet F → (G σ (n+1)).law ((P.stage n).preceding ⁻¹' P.stop n ∩ P.record (n+1) ⁻¹' F) = (G σ n).law (P.stop n ∩ P.record n ⁻¹' F)) ∧ (⨅ κ : RealOutput (ℕ × D), ⨆ σ : DensityState (Fin e), ∫⁻ z : ℝ, ENNReal.ofReal |z - θ σ| ∂(((G σ N).law.map (P.record N)).bind κ.kernel)) = ENNReal.ofReal (Real.log e / (2 * β)) := by classical
    clear hpadding
    letI : NeZero e := ⟨by omega⟩
    dsimp only
    have hunitary {A : Type} [Fintype A] [DecidableEq A] (H : Matrix A A ℂ) (hH : H.IsHermitian) (t : ℝ) : actualWait H t ∈ unitary (Matrix A A ℂ) := by letI : NormedRing (Matrix A A ℂ) := Matrix.instL2OpNormedRing
                                                                                                                                                         letI : NormedAlgebra ℂ (Matrix A A ℂ) := Matrix.instL2OpNormedAlgebra
                                                                                                                                                         letI : NormedAlgebra ℚ (Matrix A A ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
                                                                                                                                                         change NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) ∈ unitary (Matrix A A ℂ); apply exp_mem_unitary_of_mem_skewAdjoint
                                                                                                                                                         rw [skewAdjoint.mem_iff, star_smul]
                                                                                                                                                         have hh : star H = H := hH.eq
                                                                                                                                                         rw [hh]
                                                                                                                                                         have hc : star (-Complex.I * (t : ℂ)) = -(-Complex.I * (t : ℂ)) := by simp
                                                                                                                                                         rw [hc, neg_smul]
    have hfactor {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (H : Matrix A A ℂ) (t : ℝ) : actualWait (H ⊗ₖ (1 : Matrix B B ℂ)) t = actualWait H t ⊗ₖ (1 : Matrix B B ℂ) := by letI : NormedRing (Matrix A A ℂ) := Matrix.instL2OpNormedRing
                                                                                                                                                                                                       letI : NormedAlgebra ℂ (Matrix A A ℂ) := Matrix.instL2OpNormedAlgebra
                                                                                                                                                                                                       letI : NormedAlgebra ℚ (Matrix A A ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
                                                                                                                                                                                                       letI : NormedRing (Matrix (A × B) (A × B) ℂ) := Matrix.instL2OpNormedRing
                                                                                                                                                                                                       letI : NormedAlgebra ℂ (Matrix (A × B) (A × B) ℂ) := Matrix.instL2OpNormedAlgebra
                                                                                                                                                                                                       letI : NormedAlgebra ℚ (Matrix (A × B) (A × B) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
                                                                                                                                                                                                       change NormedSpace.exp ((-Complex.I * (t : ℂ)) • (H ⊗ₖ (1 : Matrix B B ℂ))) = NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) ⊗ₖ (1 : Matrix B B ℂ)
                                                                                                                                                                                                       let L : Matrix A A ℂ →ₐ[ℂ] Matrix (A × B) (A × B) ℂ :=
                                                                                                                                                                                                         { toFun := fun X => X ⊗ₖ (1 : Matrix B B ℂ)
                                                                                                                                                                                                           map_zero' := by simp
                                                                                                                                                                                                           map_one' := one_kronecker_one
                                                                                                                                                                                                           map_add' := fun X Y => add_kronecker X Y _
                                                                                                                                                                                                           map_mul' := fun X Y => by rw [← mul_kronecker_mul, one_mul]
                                                                                                                                                                                                           commutes' := by intro c
                                                                                                                                                                                                                           simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one] }
                                                                                                                                                                                                       have he := map_exp L L.toLinearMap.continuous_of_finiteDimensional ((-Complex.I * (t : ℂ)) • H)
                                                                                                                                                                                                       simpa only [L, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, smul_kronecker] using he.symm
    have hmeasWait {S : Type u} {A : Type} [MeasurableSpace S] [Fintype A] [DecidableEq A] (H : Matrix A A ℂ) (t : S → ℝ) (ht : Measurable t) : Measurable (fun s => actualWait H (t s)) := by letI : NormedRing (Matrix A A ℂ) := Matrix.instL2OpNormedRing
                                                                                                                                                                                               letI : NormedAlgebra ℂ (Matrix A A ℂ) := Matrix.instL2OpNormedAlgebra
                                                                                                                                                                                               letI : NormedAlgebra ℚ (Matrix A A ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
                                                                                                                                                                                               change Measurable (fun s => NormedSpace.exp ((-Complex.I * (t s : ℂ)) • H))
                                                                                                                                                                                               have hu : Continuous (fun x : ℝ => exp ((-Complex.I * (x : ℂ)) • H)) := exp_continuous.comp ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)
                                                                                                                                                                                               change Measurable (fun s i j => exp ((-Complex.I * (t s : ℂ)) • H) i j); apply measurable_pi_lambda
                                                                                                                                                                                               intro i; apply measurable_pi_lambda
                                                                                                                                                                                               intro j; exact ((continuous_apply_apply i j).comp hu).measurable.comp ht
    have hwaitingChannel {S : Type u} {A : Type} [MeasurableSpace S] [Fintype A] [DecidableEq A] (U : S → Matrix A A ℂ) (hU : Measurable U) (hunit : ∀ s, U s ∈ unitary (Matrix A A ℂ)) :
        ∃ W : S → D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel A A, (∀ s X, CStarMatrix.ofMatrix.symm ((W s).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U s * X * (U s)ᴴ) ∧ (∀ a b i j, Measurable (fun s => CStarMatrix.ofMatrix.symm ((W s).toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)) := by classical
      have hw (s : S) : ∃ W : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel A A,
          ∀ X, CStarMatrix.ofMatrix.symm (W.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U s * X * (U s)ᴴ := by
        have hk : (∑ _ : Unit, (U s)ᴴ * U s) = 1 := by simpa only [Finset.univ_unique, Finset.sum_singleton, star_eq_conjTranspose] using (Unitary.mem_iff.mp (hunit s)).1
        obtain ⟨W, hW⟩ := finite_kraus_quantum_channel (fun _ : Unit => U s) hk
        exact ⟨W, fun X => by simpa using hW X⟩
      choose W hW using hw
      refine ⟨W, hW, ?_⟩
      intro a b i j
      simp_rw [hW, Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact Finset.measurable_sum _ (fun k _ => (Finset.measurable_sum _ (fun l _ => (((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hU)).mul measurable_const))).mul (Complex.continuous_conj.measurable.comp ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hU))))
    have hwaited {H T : Type u} {A : Type} [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] (stop : Set H) (J : RawAdaptiveStage H T A stop) (W : H → D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel A A) (hWmeas : ∀ a b i j, Measurable (fun h => CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)) :
        ∃ K : RawAdaptiveStage H T A stop, K.preceding = J.preceding ∧ (∀ h F X, CStarMatrix.ofMatrix.symm (K.operation h (K.embed h ⁻¹' F) (CStarMatrix.ofMatrix X)) = CStarMatrix.ofMatrix.symm (J.operation h (J.embed h ⁻¹' F) ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))) := by
      classical
      letI : ∀ h, MeasurableSpace (J.Outcome h) := J.outcomeMeasurable
      let Ψ (h : H) (F : Set (J.Outcome h)) : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ) :=
        { toLinearMap := (J.operation h F).toLinearMap.comp (W h).toCompletelyPositiveMap.toLinearMap
          map_cstarMatrix_nonneg' := by intro k X hX
                                        have hW := (W h).toCompletelyPositiveMap.map_cstarMatrix_nonneg X hX
                                        have hΦ := (J.operation h F).map_cstarMatrix_nonneg (X.map (W h).toCompletelyPositiveMap) hW
                                        have he : (X.map (W h).toCompletelyPositiveMap).map (J.operation h F) = X.map (fun x => J.operation h F ((W h).toCompletelyPositiveMap x)) := by ext i j
                                                                                                                                                                                         rfl
                                        change 0 ≤ X.map (fun x => J.operation h F ((W h).toCompletelyPositiveMap x)); rw [← he]
                                        exact hΦ }
      have he (h : H) (F : Set (J.Outcome h)) (X : Matrix A A ℂ) : CStarMatrix.ofMatrix.symm (Ψ h F (CStarMatrix.ofMatrix X)) = CStarMatrix.ofMatrix.symm (J.operation h F ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) := rfl
      have hexpand (h : H) (F : Set (J.Outcome h)) (X : Matrix A A ℂ) : CStarMatrix.ofMatrix.symm (Ψ h F (CStarMatrix.ofMatrix X)) = ∑ a, ∑ b, CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) a b • CStarMatrix.ofMatrix.symm (J.operation h F (CStarMatrix.ofMatrix (Matrix.single a b 1))) := by let Y := CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X))
                                                                                                                                                                                                                                                                                                                                       let F₀ : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp ((J.operation h F).toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
                                                                                                                                                                                                                                                                                                                                       have hY : Y = ∑ a, ∑ b, Y a b • Matrix.single a b 1 := by ext a b
                                                                                                                                                                                                                                                                                                                                                                                                 simp [Matrix.single, Matrix.sum_apply, ite_and]
                                                                                                                                                                                                                                                                                                                                       change F₀ Y = _
                                                                                                                                                                                                                                                                                                                                       conv_lhs => rw [hY]
                                                                                                                                                                                                                                                                                                                                       rw [map_sum]; simp only [map_sum, map_smul]
                                                                                                                                                                                                                                                                                                                                       rfl
      let K : RawAdaptiveStage H T A stop :=
        { Outcome := J.Outcome
          outcomeMeasurable := J.outcomeMeasurable
          embed := J.embed
          legal := J.legal
          preceding := J.preceding
          measurable_preceding := J.measurable_preceding
          preceding_embed := J.preceding_embed
          operation := Ψ
          empty_operation := by intro h X
                                simpa only [he, CStarMatrix.ofMatrix.apply_symm_apply] using J.empty_operation h (CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))
          additive_operation := by intro h f hf hd X i j
                                   simpa only [he, CStarMatrix.ofMatrix.apply_symm_apply] using J.additive_operation h f hf hd (CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) i j
          trace_preserving := by intro h hs X
                                 have ht := J.trace_preserving h hs (CStarMatrix.ofMatrix.symm ((W h).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))
                                 simp only [CStarMatrix.ofMatrix.apply_symm_apply] at ht
                                 rw [he, ht]; exact (W h).trace_preserving (CStarMatrix.ofMatrix X)
          measurable_operation := by intro F hF a b i j
                                     simp_rw [hexpand, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
                                     exact Finset.measurable_sum _ (fun c _ => Finset.measurable_sum _ (fun d _ => (hWmeas a b c d).mul (J.measurable_operation F hF c d i j))) }
      exact ⟨K, rfl, fun h F X => he h (J.embed h ⁻¹' F) X⟩
    have hstopped {H T : Type u} {A : Type} [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] (stop : Set H) (hstop : MeasurableSet stop) (J : RawAdaptiveStage H T A stop) (cem : H → T) (hcem : Measurable cem) (hcem_prev : ∀ h, J.preceding (cem h) = h) :
        ∃ K : LegalAdaptiveStage H T A, K.preceding = J.preceding ∧ (∀ h F X, CStarMatrix.ofMatrix.symm (K.operation h (K.embed h ⁻¹' F) (CStarMatrix.ofMatrix X)) = if h ∈ stop then (if cem h ∈ F then X else 0) else
              CStarMatrix.ofMatrix.symm (J.operation h (J.embed h ⁻¹' F) (CStarMatrix.ofMatrix X))) := by
      classical
      letI : ∀ h, MeasurableSpace (J.Outcome h) := J.outcomeMeasurable
      let O (h : H) := Unit ⊕ J.Outcome h
      letI (h : H) : MeasurableSpace (O h) := inferInstanceAs (MeasurableSpace (Unit ⊕ J.Outcome h))
      let embed (h : H) : O h → T := Sum.elim (fun _ => cem h) (J.embed h)
      have hlegal (h : H) (F : Set T) (hF : MeasurableSet F) : MeasurableSet (embed h ⁻¹' F) := by apply measurableSet_sum_iff.mpr
                                                                                                   exact ⟨hF.preimage measurable_const, J.legal h F hF⟩
      let idCP : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ) :=
        { toLinearMap := LinearMap.id
          map_cstarMatrix_nonneg' := by intro k X hX; simpa using hX }
      let zeroCP : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ) :=
        { toLinearMap := 0
          map_cstarMatrix_nonneg' := by intro k X hX
                                        have hz : X.map (0 : CStarMatrix A A ℂ →ₗ[ℂ] CStarMatrix A A ℂ) = 0 := by ext i j
                                                                                                                  rfl
                                        rw [hz] }
      let Ψ (h : H) (F : Set (O h)) := if h ∈ stop then (if Sum.inl () ∈ F then idCP else zeroCP) else
          J.operation h (Sum.inr ⁻¹' F)
      have he (h : H) (F : Set (O h)) (X : Matrix A A ℂ) : CStarMatrix.ofMatrix.symm (Ψ h F (CStarMatrix.ofMatrix X)) = if h ∈ stop then (if Sum.inl () ∈ F then X else 0) else
              CStarMatrix.ofMatrix.symm (J.operation h (Sum.inr ⁻¹' F) (CStarMatrix.ofMatrix X)) := by
        by_cases hs : h ∈ stop
        · by_cases hc : Sum.inl () ∈ F
          · simp only [Ψ, if_pos hs, if_pos hc]
            change CStarMatrix.ofMatrix.symm (CStarMatrix.ofMatrix X) = X; exact CStarMatrix.ofMatrix.symm_apply_apply X
          · simp only [Ψ, if_pos hs, if_neg hc]
            rfl
        · simp only [Ψ, if_neg hs]
      have heval (h : H) (F : Set (O h)) (X : Matrix A A ℂ) (i j : A) : CStarMatrix.ofMatrix.symm (Ψ h F (CStarMatrix.ofMatrix X)) i j = if h ∈ stop then (if Sum.inl () ∈ F then X i j else 0) else
              CStarMatrix.ofMatrix.symm (J.operation h (Sum.inr ⁻¹' F) (CStarMatrix.ofMatrix X)) i j := by
        rw [he]
        by_cases hs : h ∈ stop <;> by_cases hc : Sum.inl () ∈ F <;> simp [hs, hc]
      have hretained (h : H) (F : Set T) (X : Matrix A A ℂ) : CStarMatrix.ofMatrix.symm (Ψ h (embed h ⁻¹' F) (CStarMatrix.ofMatrix X)) = if h ∈ stop then (if cem h ∈ F then X else 0) else
              CStarMatrix.ofMatrix.symm (J.operation h (J.embed h ⁻¹' F) (CStarMatrix.ofMatrix X)) := by
        rw [he]; rfl
      let D (h : H) : ComplexMeasure (O h) := (Measure.dirac (Sum.inl () : O h)).toSignedMeasure.toComplexMeasure 0
      have hdirac (Z : Type u) [MeasurableSpace Z] (z : Z) (F : Set Z) (hF : MeasurableSet F) : (Measure.dirac z).toSignedMeasure.toComplexMeasure 0 F = if z ∈ F then 1 else 0 := by by_cases hc : z ∈ F <;> apply Complex.ext <;>
                                                                                                                                                                                        simp [hc, Set.indicator, SignedMeasure.toComplexMeasure_apply, Measure.toSignedMeasure_apply_measurable hF, Measure.real, Measure.dirac_apply' _ hF]
      have hD (h : H) (F : Set (O h)) (hF : MeasurableSet F) : D h F = if Sum.inl () ∈ F then 1 else 0 := by exact hdirac (O h) (Sum.inl ()) F hF
      let K : LegalAdaptiveStage H T A :=
        { Outcome := O
          outcomeMeasurable := fun h => inferInstance
          embed := embed
          legal := hlegal
          preceding := J.preceding
          measurable_preceding := J.measurable_preceding
          preceding_embed := by intro h o
                                cases o with
                                | inl x => exact hcem_prev h
                                | inr x => exact J.preceding_embed h x
          operation := Ψ
          empty_operation := by intro h X
                                rw [he]
                                by_cases hs : h ∈ stop
                                · simp [hs]
                                · simpa only [if_neg hs, Set.preimage_empty] using J.empty_operation h X
          additive_operation := by intro h f hf hd X i j
                                   by_cases hs : h ∈ stop
                                   · have ht := ((D h).m_iUnion hf hd).mul_right (X i j)
                                     simpa only [heval, if_pos hs, hD h _ (hf _), hD h _ (MeasurableSet.iUnion hf), ite_mul, one_mul, zero_mul] using ht
                                   · simpa only [heval, if_neg hs, Set.preimage_iUnion] using J.additive_operation h (fun n => Sum.inr ⁻¹' f n) (fun n => (hf n).preimage measurable_inr) (fun m n hmn => (hd hmn).preimage Sum.inr) X i j
          trace_preserving := by intro h X
                                 rw [he]
                                 by_cases hs : h ∈ stop
                                 · simp [hs]
                                 · simpa only [if_neg hs, Set.preimage_univ] using J.trace_preserving h hs X
          measurable_operation := by intro F hF a b i j
                                     have hentry (h : H) : CStarMatrix.ofMatrix.symm (Ψ h (embed h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j = if h ∈ stop then (if cem h ∈ F then (Matrix.single a b (1 : ℂ)) i j else 0) else
                                             CStarMatrix.ofMatrix.symm (J.operation h (J.embed h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j := by
                                       rw [hretained]
                                       by_cases hs : h ∈ stop <;> by_cases hc : cem h ∈ F <;> simp [hs, hc]
                                     simp_rw [hentry]
                                     exact Measurable.piecewise hstop (Measurable.piecewise (hF.preimage hcem) measurable_const measurable_const) (J.measurable_operation F hF a b i j) }
      exact ⟨K, rfl, hretained⟩
    have hdomain {H T : Type u} {A : Type} [MeasurableSpace H] [MeasurableSpace T] [Fintype A] [DecidableEq A] (J : ActualEventStage H T A) : MeasurableSet (normalizationDomain J) ∧ (∀ h, h ∈ normalizationDomain J ↔ ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm (J.operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X) := by classical
                                                                                                                                                                                                                                                                                                                                                               constructor
                                                                                                                                                                                                                                                                                                                                                               · change MeasurableSet {h | ∀ a b, _}
                                                                                                                                                                                                                                                                                                                                                                 simp only [Set.setOf_forall]
                                                                                                                                                                                                                                                                                                                                                                 apply MeasurableSet.iInter
                                                                                                                                                                                                                                                                                                                                                                 intro a; apply MeasurableSet.iInter
                                                                                                                                                                                                                                                                                                                                                                 intro b; apply measurableSet_eq_fun
                                                                                                                                                                                                                                                                                                                                                                 · change Measurable (fun h => ∑ i, CStarMatrix.ofMatrix.symm (J.operation h Set.univ (CStarMatrix.ofMatrix (Matrix.single a b 1))) i i)
                                                                                                                                                                                                                                                                                                                                                                   apply Finset.measurable_sum
                                                                                                                                                                                                                                                                                                                                                                   intro i hi; simpa only [Set.preimage_univ] using J.measurable_operation Set.univ MeasurableSet.univ a b i i
                                                                                                                                                                                                                                                                                                                                                                 · exact measurable_const
                                                                                                                                                                                                                                                                                                                                                               · intro h
                                                                                                                                                                                                                                                                                                                                                                 constructor
                                                                                                                                                                                                                                                                                                                                                                 · intro hh X
                                                                                                                                                                                                                                                                                                                                                                   let F : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp ((J.operation h Set.univ).toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
                                                                                                                                                                                                                                                                                                                                                                   have hexpand : X = ∑ a, ∑ b, X a b • Matrix.single a b 1 := by ext a b
                                                                                                                                                                                                                                                                                                                                                                                                                                  simp [Matrix.single, Matrix.sum_apply, ite_and]
                                                                                                                                                                                                                                                                                                                                                                   change Matrix.trace (F X) = Matrix.trace X
                                                                                                                                                                                                                                                                                                                                                                   conv_lhs => rw [hexpand]
                                                                                                                                                                                                                                                                                                                                                                   rw [map_sum]; simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
                                                                                                                                                                                                                                                                                                                                                                   conv_rhs => rw [hexpand]
                                                                                                                                                                                                                                                                                                                                                                   simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
                                                                                                                                                                                                                                                                                                                                                                   apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                                                                                                                   intro a ha; apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                                                                                                                   intro b hb; exact congrArg (fun z : ℂ => X a b * z) (hh a b)
                                                                                                                                                                                                                                                                                                                                                                 · intro hh a b
                                                                                                                                                                                                                                                                                                                                                                   exact hh (Matrix.single a b 1)
    let stop' (n : ℕ) := P.stop n ∪ (normalizationDomain (P.stage n))ᶜ
    have hstop' (n : ℕ) : MeasurableSet (stop' n) := (P.measurable_stop n).union (hdomain (P.stage n)).1.compl
    let raw (n : ℕ) : RawAdaptiveStage (H n) (H (n+1)) A (stop' n) :=
      { Outcome := (P.stage n).Outcome
        outcomeMeasurable := (P.stage n).outcomeMeasurable
        embed := (P.stage n).embed
        legal := (P.stage n).legal
        preceding := (P.stage n).preceding
        measurable_preceding := (P.stage n).measurable_preceding
        preceding_embed := (P.stage n).preceding_embed
        operation := (P.stage n).operation
        empty_operation := (P.stage n).empty_operation
        additive_operation := (P.stage n).additive_operation
        trace_preserving := fun h hh => (hdomain (P.stage n)).2 h |>.mp (by have hn : h ∈ normalizationDomain (P.stage n) := by
                                                                              by_contra hn
                                                                              exact hh (Or.inr hn)
                                                                            exact hn)
        measurable_operation := (P.stage n).measurable_operation }
    have heffective (n : ℕ) : ∃ K : LegalAdaptiveStage (H n) (H (n+1)) A, (∀ h E X, CStarMatrix.ofMatrix.symm (K.operation h (K.embed h ⁻¹' E) (CStarMatrix.ofMatrix X)) = if h ∈ stop' n then (if P.cemetery n h ∈ E then X else 0) else
            CStarMatrix.ofMatrix.symm ((P.stage n).operation h ((P.stage n).embed h ⁻¹' E) (CStarMatrix.ofMatrix (actualWait H_A (P.time n h) * X * (actualWait H_A (P.time n h))ᴴ)))) := by
      obtain ⟨W, hW, hWm⟩ := hwaitingChannel (fun h => actualWait H_A (P.time n h)) (hmeasWait H_A (P.time n) (P.measurable_time n)) (fun h => hunitary H_A hH_A (P.time n h))
      obtain ⟨J, hJprev, hJ⟩ := hwaited (stop' n) (raw n) W hWm
      obtain ⟨K, hKprev, hK⟩ := hstopped (stop' n) (hstop' n) J (P.cemetery n) (P.measurable_cemetery n) (fun h => by rw [hJprev]; exact P.preceding_cemetery n h)
      refine ⟨K, ?_⟩
      intro h E X; rw [hK, hJ]
      have hw := hW h X
      simpa only [raw, stop', CStarMatrix.ofMatrix.apply_symm_apply] using congrArg (fun Z : Matrix A A ℂ => if h ∈ stop' n then (if P.cemetery n h ∈ E then X else 0) else
          CStarMatrix.ofMatrix.symm ((P.stage n).operation h ((P.stage n).embed h ⁻¹' E) (CStarMatrix.ofMatrix Z))) hw
    choose K hK using heffective
    have hruntime {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Φ : CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ)) (U : Matrix A A ℂ) (V : Matrix (A × B) (A × B) ℂ) (hV : V = U ⊗ₖ (1 : Matrix B B ℂ)) (X : Matrix A A ℂ) (σ : Matrix B B ℂ) :
        let f := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
        PhyslibLeaf.MatrixMap.kron f LinearMap.id (V * (X ⊗ₖ σ) * Vᴴ) = CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix (U * X * Uᴴ))) ⊗ₖ σ := by classical
      dsimp only
      let f := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
      have hwait : V * (X ⊗ₖ σ) * Vᴴ = (U * X * Uᴴ) ⊗ₖ σ := by rw [hV, Matrix.conjTranspose_kronecker]
                                                               rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp
      rw [hwait]; change PhyslibLeaf.MatrixMap.kron f LinearMap.id ((U * X * Uᴴ) ⊗ₖ σ) = f (U * X * Uᴴ) ⊗ₖ σ
      have hexpand : U * X * Uᴴ = ∑ i, ∑ j, (U * X * Uᴴ) i j • Matrix.single i j (1 : ℂ) := by ext i j
                                                                                               simp [Matrix.single, Matrix.sum_apply, ite_and]
      have hlinear : f (U * X * Uᴴ) = ∑ i, ∑ j, (U * X * Uᴴ) i j • f (Matrix.single i j 1) := by
        conv_lhs => rw [hexpand]
        simp only [map_sum, map_smul]
      ext ⟨i,a⟩ ⟨j,b⟩
      rw [PhyslibLeaf.MatrixMap.kron_def, hlinear]; simp [LinearMap.id_apply, Matrix.single, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ite_and, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    have hcompat (σ : Matrix (Fin e) (Fin e) ℂ) (n : ℕ) (h : H n) (E : Set (H (n+1))) (X : Matrix A A ℂ) : completedStoppedStep P H_A n h E (X ⊗ₖ σ) = CStarMatrix.ofMatrix.symm ((K n).operation h ((K n).embed h ⁻¹' E) (CStarMatrix.ofMatrix X)) ⊗ₖ σ := by rw [hK]
                                                                                                                                                                                                                                                               dsimp only [stop']
                                                                                                                                                                                                                                                               by_cases hs : h ∈ P.stop n ∪ (normalizationDomain (P.stage n))ᶜ
                                                                                                                                                                                                                                                               · by_cases hc : P.cemetery n h ∈ E
                                                                                                                                                                                                                                                                 · simp only [completedStoppedStep, stop', if_pos hs, if_pos hc]
                                                                                                                                                                                                                                                                 · simp only [completedStoppedStep, stop', if_pos hs, if_neg hc, Matrix.zero_kronecker]
                                                                                                                                                                                                                                                               · simp only [completedStoppedStep, stop', if_neg hs]
                                                                                                                                                                                                                                                                 exact hruntime ((P.stage n).operation h ((P.stage n).embed h ⁻¹' E)) (actualWait H_A (P.time n h)) (actualWait (H_A ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ)) (P.time n h)) (hfactor H_A (P.time n h)) X σ
    have hwhole {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (H : ℕ → Type u) [∀ n, MeasurableSpace (H n)] (J : ∀ n, LegalAdaptiveStage (H n) (H (n+1)) A) (L : ∀ n, H n → Set (H (n+1)) → Matrix (A × B) (A × B) ℂ → Matrix (A × B) (A × B) ℂ) (hcompat : ∀ σ n h E X, L n h E (X ⊗ₖ σ) = CStarMatrix.ofMatrix.symm ((J n).operation h ((J n).embed h ⁻¹' E) (CStarMatrix.ofMatrix X)) ⊗ₖ σ) (h₀ : H 0) (ρ₀ : Matrix A A ℂ) (hρ₀ : ρ₀.PosSemidef) (hρ₀trace : Matrix.trace ρ₀ = 1) (M : ℕ) :
        ∃ S : ∀ n, ActualHistory (H n) A, (S 0).law = Measure.dirac h₀ ∧ (∀ n, (S (n+1)).law.map (J n).preceding = (S n).law) ∧ (∀ n E, MeasurableSet E → ∀ i j, (∫ h in E, (S (n+1)).density h i j ∂(S (n+1)).law) = ∫ h, CStarMatrix.ofMatrix.symm ((J n).operation h ((J n).embed h ⁻¹' E) (CStarMatrix.ofMatrix ((S n).density h))) i j ∂(S n).law) ∧ (∀ (σ : Matrix B B ℂ), σ.PosSemidef → Matrix.trace σ = 1 →
            ∀ G : ∀ n, ActualHistory (H n) (A × B),
            (G 0).law = Measure.dirac h₀ →
            (G 0).density =ᵐ[(G 0).law] (fun _ => ρ₀ ⊗ₖ σ) →
            (∀ n, n < M → ∀ E, MeasurableSet E → ∀ i j, (∫ h in E, (G (n+1)).density h i j ∂(G (n+1)).law) = ∫ h, L n h E ((G n).density h) i j ∂(G n).law) →
            ∀ n, n ≤ M → (G n).law = (S n).law ∧ (G n).density =ᵐ[(S n).law] (fun h => (S n).density h ⊗ₖ σ)) := by classical
      have hstep {H T : Type u} {I : Type} [MeasurableSpace H] [MeasurableSpace T] [Fintype I] [DecidableEq I] (μ : Measure H) [IsFiniteMeasure μ] (r₀ : H → Matrix I I ℂ) (hr₀ : Measurable r₀) (hstate : ∀ h, (r₀ h).PosSemidef ∧ Matrix.trace (r₀ h) = 1) (O : H → Type u) [∀ h, MeasurableSpace (O h)] (ι : ∀ h, O h → T) (hlegal : ∀ h F, MeasurableSet F → MeasurableSet (ι h ⁻¹' F)) (p : T → H) (hp : Measurable p) (hπι : ∀ h o, p (ι h o) = h) (Ψ : ∀ h, Set (O h) → CompletelyPositiveMap (CStarMatrix I I ℂ) (CStarMatrix I I ℂ)) (hΨzero : ∀ h X, CStarMatrix.ofMatrix.symm (Ψ h ∅ (CStarMatrix.ofMatrix X)) = 0) (hΨadd : ∀ h (f : ℕ → Set (O h)), (∀ n, MeasurableSet (f n)) → Pairwise (fun m n => Disjoint (f m) (f n)) → ∀ X i j, HasSum (fun n => CStarMatrix.ofMatrix.symm (Ψ h (f n) (CStarMatrix.ofMatrix X)) i j) (CStarMatrix.ofMatrix.symm (Ψ h (⋃ n, f n) (CStarMatrix.ofMatrix X)) i j)) (hΨTP : ∀ h X, Matrix.trace (CStarMatrix.ofMatrix.symm (Ψ h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X) (hmeas : ∀ F, MeasurableSet F → ∀ a b i j, Measurable (fun h => CStarMatrix.ofMatrix.symm (Ψ h (ι h ⁻¹' F) (CStarMatrix.ofMatrix (Matrix.single a b 1))) i j)) (base : Matrix I I ℂ) (hbase : base.PosSemidef) (hbaseTrace : Matrix.trace base = 1) :
          ∃ K : (I → ℂ) → Kernel H T, (∀ v, IsFiniteKernel (K v)) ∧ (∀ v h F, MeasurableSet F → K v h F = ENNReal.ofReal ((star v ⬝ᵥ (CStarMatrix.ofMatrix.symm (Ψ h (ι h ⁻¹' F) (CStarMatrix.ofMatrix (r₀ h))) *ᵥ v)).re)) ∧
            ∃ (N : I → I → ComplexMeasure (T)) (P : Kernel H T) (τ : Measure (T))
            (ρ : T → Matrix I I ℂ),
            IsMarkovKernel P ∧ τ = μ.bind P ∧ IsFiniteMeasure τ ∧ τ.map p = μ ∧
            (∀ S, MeasurableSet S → Matrix.trace (fun i j => N i j S) = ((τ S).toReal : ℂ)) ∧
            Measurable ρ ∧ Integrable ρ τ ∧
            (∀ x, (ρ x).PosSemidef ∧ Matrix.trace (ρ x) = 1) ∧
            (∀ S, MeasurableSet S → ∀ i j, N i j S = ∫ h, CStarMatrix.ofMatrix.symm (Ψ h (ι h ⁻¹' S) (CStarMatrix.ofMatrix (r₀ h))) i j ∂μ) ∧
            (∀ S, MeasurableSet S → Matrix.PosSemidef (fun i j => N i j S)) ∧
            (∀ S, MeasurableSet S → ∀ v : I → ℂ, star v ⬝ᵥ ((fun i j => N i j S : Matrix I I ℂ) *ᵥ v) = (((μ.bind (K v)) S).toReal : ℂ)) ∧
            (∀ S, MeasurableSet S → ∀ i j, (∫ x in S, ρ x i j ∂τ) = N i j S) := by classical
        let Φ (h : H) (F : Set T) := Ψ h (ι h ⁻¹' F)
        have hzero (h : H) (X : Matrix I I ℂ) : CStarMatrix.ofMatrix.symm (Φ h ∅ (CStarMatrix.ofMatrix X)) = 0 := by simpa only [Φ, Set.preimage_empty] using hΨzero h X
        have hadd (h : H) (f : ℕ → Set T) (hf : ∀ n, MeasurableSet (f n)) (hd : Pairwise (fun m n => Disjoint (f m) (f n))) (X : Matrix I I ℂ) (i j : I) : HasSum (fun n => CStarMatrix.ofMatrix.symm (Φ h (f n) (CStarMatrix.ofMatrix X)) i j) (CStarMatrix.ofMatrix.symm (Φ h (⋃ n, f n) (CStarMatrix.ofMatrix X)) i j) := by have hd' : Pairwise (fun m n => Disjoint (ι h ⁻¹' f m) (ι h ⁻¹' f n)) := by intro m n hmn
                                                                                                                                                                                                                                                                                                                                                                                                            exact (hd hmn).preimage (ι h)
                                                                                                                                                                                                                                                                                                                                simpa only [Φ, Set.preimage_iUnion] using hΨadd h (fun n => ι h ⁻¹' f n) (fun n => hlegal h (f n) (hf n)) hd' X i j
        have hTP (h : H) (X : Matrix I I ℂ) : Matrix.trace (CStarMatrix.ofMatrix.symm (Φ h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X := by simpa only [Φ, Set.preimage_univ] using hΨTP h X
        have hscalar : ∃ K : (I → ℂ) → Kernel H T, (∀ v, IsFiniteKernel (K v)) ∧ (∀ v h E, MeasurableSet E → K v h E = ENNReal.ofReal ((star v ⬝ᵥ (CStarMatrix.ofMatrix.symm (Φ h E (CStarMatrix.ofMatrix (r₀ h))) *ᵥ v)).re)) ∧ (∀ v h E, MeasurableSet E → K v h E ≤ ENNReal.ofReal (∑ i, Complex.normSq (v i))) := by classical
                                                                                                                                                                                                                                                                                                                         let A (h : H) (E : Set T) : Matrix I I ℂ := CStarMatrix.ofMatrix.symm (Φ h E (CStarMatrix.ofMatrix (r₀ h)))
                                                                                                                                                                                                                                                                                                                         have hApos (h : H) (E : Set T) : (A h E).PosSemidef := by apply Matrix.nonneg_iff_posSemidef.mp
                                                                                                                                                                                                                                                                                                                                                                                   apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
                                                                                                                                                                                                                                                                                                                                                                                   apply map_nonneg (Φ h E)
                                                                                                                                                                                                                                                                                                                                                                                   exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hstate h).1.nonneg
                                                                                                                                                                                                                                                                                                                         have hAmeas (E : Set T) (hE : MeasurableSet E) (i j : I) : Measurable (fun h => A h E i j) := by have expand (h : H) : A h E = ∑ a, ∑ b, r₀ h a b • CStarMatrix.ofMatrix.symm (Φ h E (CStarMatrix.ofMatrix (Matrix.single a b 1))) := by
                                                                                                                                                                                                                                                                                                                                                                                                                            let F : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp ((Φ h E).toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
                                                                                                                                                                                                                                                                                                                                                                                                                            have he : r₀ h = ∑ a, ∑ b, r₀ h a b • Matrix.single a b 1 := by ext a b
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            simp [Matrix.single, Matrix.sum_apply, ite_and]
                                                                                                                                                                                                                                                                                                                                                                                                                            change F (r₀ h) = _
                                                                                                                                                                                                                                                                                                                                                                                                                            conv_lhs => rw [he]
                                                                                                                                                                                                                                                                                                                                                                                                                            rw [map_sum]; simp only [map_sum, map_smul]
                                                                                                                                                                                                                                                                                                                                                                                                                            rfl
                                                                                                                                                                                                                                                                                                                                                                                                                          simp_rw [expand, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
                                                                                                                                                                                                                                                                                                                                                                                                                          exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ => ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hr₀)).mul (hmeas E hE a b i j)))
                                                                                                                                                                                                                                                                                                                         let C (h : H) (i j : I) : ComplexMeasure T :=
                                                                                                                                                                                                                                                                                                                           { measureOf' := fun E => if MeasurableSet E then A h E i j else 0
                                                                                                                                                                                                                                                                                                                             empty' := by simp only [if_pos MeasurableSet.empty]
                                                                                                                                                                                                                                                                                                                                          exact congrFun (congrFun (hzero h (r₀ h)) i) j
                                                                                                                                                                                                                                                                                                                             not_measurable' := by intro E hE; simp [hE]
                                                                                                                                                                                                                                                                                                                             m_iUnion' := by intro f hf hd
                                                                                                                                                                                                                                                                                                                                             simpa only [if_pos (hf _), if_pos (MeasurableSet.iUnion hf)] using hadd h f hf hd (r₀ h) i j }
                                                                                                                                                                                                                                                                                                                         have hC (h : H) (i j : I) (E : Set T) (hE : MeasurableSet E) : C h i j E = A h E i j := by simp [C, hE]
                                                                                                                                                                                                                                                                                                                         have htrace (h : H) (E : Set T) (hE : MeasurableSet E) : (Matrix.trace (A h E)).re ≤ 1 := by have hsplit : A h Set.univ = A h E + A h Eᶜ := by ext i j
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        have ht := (C h i j).of_union disjoint_compl_right hE hE.compl
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        simpa [hC, hE, hE.compl, Matrix.add_apply] using ht
                                                                                                                                                                                                                                                                                                                                                                                                                      have hn := (hApos h Eᶜ).trace_nonneg
                                                                                                                                                                                                                                                                                                                                                                                                                      have htot : Matrix.trace (A h Set.univ) = 1 := by exact (hTP h (r₀ h)).trans (hstate h).2
                                                                                                                                                                                                                                                                                                                                                                                                                      rw [hsplit, Matrix.trace_add, Complex.ext_iff] at htot
                                                                                                                                                                                                                                                                                                                                                                                                                      have hc := htot.1
                                                                                                                                                                                                                                                                                                                                                                                                                      have hre := (Complex.nonneg_iff.mp hn).1
                                                                                                                                                                                                                                                                                                                                                                                                                      simp only [Complex.add_re, Complex.one_re] at hc
                                                                                                                                                                                                                                                                                                                                                                                                                      linarith
                                                                                                                                                                                                                                                                                                                         have hbound (h : H) (E : Set T) (hE : MeasurableSet E) (v : I → ℂ) : (star v ⬝ᵥ (A h E *ᵥ v)).re ≤ ∑ i, Complex.normSq (v i) := by let B := A h E
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hB := hApos h E
                                                                                                                                                                                                                                                                                                                                                                                                                                                            let U := hB.isHermitian.eigenvectorUnitary
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hsum : ∑ i, hB.isHermitian.eigenvalues i ≤ 1 := by simpa [hB.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum] using htrace h E hE
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hev (i : I) : hB.isHermitian.eigenvalues i ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)) hsum
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hDc : (diagonal (fun i => ((1 - hB.isHermitian.eigenvalues i : ℝ) : ℂ))).PosSemidef := by exact posSemidef_diagonal_iff.mpr (fun i => by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             exact_mod_cast (sub_nonneg.mpr (hev i)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hc := hDc.mul_mul_conjTranspose_same (U : Matrix I I ℂ)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hsub : (1 - B).PosSemidef := by change (1 - A h E).PosSemidef
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 convert hc using 1
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 have hd : diagonal (fun i => ((1 - hB.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 - diagonal (fun i => (hB.isHermitian.eigenvalues i : ℂ)) := by ext i j
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               by_cases hij : i = j <;> simp [diagonal, Matrix.one_apply, hij]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 rw [hd, mul_sub, sub_mul, mul_one]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 conv_lhs => rw [hB.isHermitian.spectral_theorem]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal, Function.comp_def]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 have hU : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 := by simpa only [Unitary.coe_star, star_eq_conjTranspose] using Unitary.coe_mul_star_self U
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 simpa only [U, Function.comp_def] using congrArg (fun Z : Matrix I I ℂ => Z - (U : Matrix I I ℂ) * diagonal (fun i => (hB.isHermitian.eigenvalues i : ℂ)) * (U : Matrix I I ℂ)ᴴ) hU.symm
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hv := hsub.re_dotProduct_nonneg v
                                                                                                                                                                                                                                                                                                                                                                                                                                                            change 0 ≤ (star v ⬝ᵥ ((1 - B) *ᵥ v)).re at hv
                                                                                                                                                                                                                                                                                                                                                                                                                                                            have hnorm : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by simp [dotProduct, Complex.re_sum, Complex.normSq_apply, Complex.mul_re]
                                                                                                                                                                                                                                                                                                                                                                                                                                                            rw [sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re, hnorm] at hv; exact sub_nonneg.mp hv
                                                                                                                                                                                                                                                                                                                         let Q (v : I → ℂ) (h : H) : SignedMeasure T := (∑ i, ∑ j, (conj (v i) * v j) • C h i j).re
                                                                                                                                                                                                                                                                                                                         have hQ (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : Q v h E = (star v ⬝ᵥ (A h E *ᵥ v)).re := by have heval : (∑ i, ∑ j, (conj (v i) * v j) • C h i j) E = star v ⬝ᵥ (A h E *ᵥ v) := by simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, hC h _ _ E hE, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             intro i _; apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             intro j _
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             ring
                                                                                                                                                                                                                                                                                                                                                                                                                                      change ((∑ i, ∑ j, (conj (v i) * v j) • C h i j) E).re = _; exact congrArg Complex.re heval
                                                                                                                                                                                                                                                                                                                         have hQpos (v : I → ℂ) (h : H) : 0 ≤[Set.univ] Q v h := by apply (VectorMeasure.restrict_le_restrict_iff (0 : SignedMeasure T) (Q v h) MeasurableSet.univ).2
                                                                                                                                                                                                                                                                                                                                                                                    intro E hE _; simpa [hQ v h E hE] using (hApos h E).re_dotProduct_nonneg v
                                                                                                                                                                                                                                                                                                                         let m (v : I → ℂ) (h : H) : Measure T := (Q v h).toMeasureOfZeroLE Set.univ MeasurableSet.univ (hQpos v h)
                                                                                                                                                                                                                                                                                                                         have hm (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : m v h E = ENNReal.ofReal (Q v h E) := by change (Q v h).toMeasureOfZeroLE Set.univ MeasurableSet.univ (hQpos v h) E = _
                                                                                                                                                                                                                                                                                                                                                                                                                                   rw [SignedMeasure.toMeasureOfZeroLE_apply (Q v h) (hQpos v h) MeasurableSet.univ hE]; simp [ENNReal.ofReal, Real.toNNReal, Set.univ_inter, (hApos h E).re_dotProduct_nonneg v, hQ v h E hE]
                                                                                                                                                                                                                                                                                                                                                                                                                                   apply Subtype.ext
                                                                                                                                                                                                                                                                                                                                                                                                                                   exact (max_eq_left ((hApos h E).re_dotProduct_nonneg v)).symm
                                                                                                                                                                                                                                                                                                                         let K (v : I → ℂ) : Kernel H T :=
                                                                                                                                                                                                                                                                                                                           { toFun := m v
                                                                                                                                                                                                                                                                                                                             measurable' := by apply Measure.measurable_of_measurable_coe
                                                                                                                                                                                                                                                                                                                                               intro E hE
                                                                                                                                                                                                                                                                                                                                               simp_rw [hm v _ E hE, hQ v _ E hE]
                                                                                                                                                                                                                                                                                                                                               apply Measurable.ennreal_ofReal
                                                                                                                                                                                                                                                                                                                                               apply Complex.measurable_re.comp
                                                                                                                                                                                                                                                                                                                                               simp only [dotProduct, mulVec, Finset.mul_sum]
                                                                                                                                                                                                                                                                                                                                               exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => measurable_const.mul ((hAmeas E hE i j).mul measurable_const))) }
                                                                                                                                                                                                                                                                                                                         have hK (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : K v h E = ENNReal.ofReal ((star v ⬝ᵥ (A h E *ᵥ v)).re) := by exact (hm v h E hE).trans (congrArg ENNReal.ofReal (hQ v h E hE))
                                                                                                                                                                                                                                                                                                                         refine ⟨K, ?_, hK, ?_⟩
                                                                                                                                                                                                                                                                                                                         · intro v
                                                                                                                                                                                                                                                                                                                           refine ⟨⟨ENNReal.ofReal (∑ i, Complex.normSq (v i)), ENNReal.ofReal_lt_top, ?_⟩⟩
                                                                                                                                                                                                                                                                                                                           intro h; rw [hK v h Set.univ MeasurableSet.univ]
                                                                                                                                                                                                                                                                                                                           exact ENNReal.ofReal_le_ofReal (hbound h Set.univ MeasurableSet.univ v)
                                                                                                                                                                                                                                                                                                                         · intro v h E hE
                                                                                                                                                                                                                                                                                                                           rw [hK v h E hE]; exact ENNReal.ofReal_le_ofReal (hbound h E hE v)
        obtain ⟨K, hKfinite, hK, hKB⟩ := hscalar
        letI (v : I → ℂ) : IsFiniteKernel (K v) := hKfinite v
        let A (h : H) (E : Set T) : Matrix I I ℂ := CStarMatrix.ofMatrix.symm (Φ h E (CStarMatrix.ofMatrix (r₀ h)))
        have hA (h : H) (E : Set T) (_ : MeasurableSet E) : (A h E).PosSemidef := by apply Matrix.nonneg_iff_posSemidef.mp
                                                                                     apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
                                                                                     apply map_nonneg (Φ h E)
                                                                                     exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hstate h).1.nonneg
        have htrace (h : H) : Matrix.trace (A h Set.univ) = 1 := (hTP h (r₀ h)).trans (hstate h).2
        have hproject (h : H) (E : Set H) (_ : MeasurableSet E) : A h (p ⁻¹' E) = if h ∈ E then A h Set.univ else 0 := by have he : ι h ⁻¹' (p ⁻¹' E) = if h ∈ E then Set.univ else ∅ := by ext o
                                                                                                                                                                                            simp only [Set.mem_preimage, hπι]
                                                                                                                                                                                            by_cases hh : h ∈ E <;> simp [hh]
                                                                                                                          change CStarMatrix.ofMatrix.symm (Ψ h (ι h ⁻¹' (p ⁻¹' E)) (CStarMatrix.ofMatrix (r₀ h))) = _; rw [he]
                                                                                                                          split_ifs
                                                                                                                          · simp only [A, Φ, Set.preimage_univ]
                                                                                                                          · exact hΨzero h (r₀ h)
        have hbound (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : (star v ⬝ᵥ (A h E *ᵥ v)).re ≤ ∑ i, Complex.normSq (v i) := by have ht := hKB v h E hE
                                                                                                                                           rw [hK v h E hE] at ht; exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i)))).mp ht
        refine ⟨K, hKfinite, hK, ?_⟩
        classical
        let e (i : I) : I → ℂ := Pi.single i 1
        let q (v : I → ℂ) (h : H) (E : Set T) := (star v ⬝ᵥ (A h E *ᵥ v)).re
        have hdiag (i j : I) (h : H) (E : Set T) : star (e i) ⬝ᵥ (A h E *ᵥ e j) = A h E i j := by simp [e, dotProduct, mulVec, Pi.single_apply]
        have hpol (h : H) (E : Set T) (hE : MeasurableSet E) (i j : I) : A h E i j = Complex.mk ((q (e i + e j) h E - q (e i - e j) h E) / 4) ((q (e i - Complex.I • e j) h E - q (e i + Complex.I • e j) h E) / 4) := by have hc := congrFun (congrFun (hA h E hE).isHermitian.eq i) j
                                                                                                                                                                                                                          simp only [conjTranspose_apply, Complex.star_def] at hc
                                                                                                                                                                                                                          simp only [Complex.ext_iff, Complex.conj_re, Complex.conj_im] at hc
                                                                                                                                                                                                                          obtain ⟨hr, hi⟩ := hc
                                                                                                                                                                                                                          apply Complex.ext <;>
                                                                                                                                                                                                                            simp [q, star_add, star_sub, star_smul, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct, dotProduct_smul, smul_dotProduct, hdiag, Complex.mul_re, Complex.mul_im] <;>
                                                                                                                                                                                                                            linarith
        have hreal (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : star v ⬝ᵥ (A h E *ᵥ v) = (q v h E : ℂ) := by apply Complex.ext
                                                                                                                         · rfl
                                                                                                                         · simpa only [Complex.ofReal_im, RCLike.im_eq_complex_im] using (hA h E hE).isHermitian.im_star_dotProduct_mulVec_self v
        have hKR (v : I → ℂ) (h : H) (E : Set T) (hE : MeasurableSet E) : (K v h E).toReal = q v h E := by rw [hK v h E hE, ENNReal.toReal_ofReal]
                                                                                                           exact (hA h E hE).re_dotProduct_nonneg v
        let ν (v : I → ℂ) := μ.bind (K v)
        have hνfinite (v : I → ℂ) : IsFiniteMeasure (ν v) := by refine ⟨?_⟩
                                                                change (μ.bind (K v)) Set.univ < ∞; rw [Measure.bind_apply MeasurableSet.univ (K v).measurable.aemeasurable]
                                                                calc
                                                                  (∫⁻ h, K v h Set.univ ∂μ) ≤ ∫⁻ _ : H, (K v).bound ∂μ := lintegral_mono (fun h => Kernel.measure_le_bound _ _ _)
                                                                  _ < ∞ := by rw [lintegral_const]
                                                                              exact ENNReal.mul_lt_top (Kernel.bound_lt_top _) (measure_lt_top μ _)
        letI (v : I → ℂ) : IsFiniteMeasure (ν v) := hνfinite v
        have hqm (v : I → ℂ) (S : Set (T)) (hS : MeasurableSet S) : Measurable (fun h => q v h S) := by have ht := ((K v).measurable_coe hS).ennreal_toReal
                                                                                                        simpa only [hKR v _ _ hS] using ht
        have hqi (v : I → ℂ) (S : Set (T)) (hS : MeasurableSet S) : Integrable (fun h => q v h S) μ := by apply Integrable.of_mem_Icc 0 (∑ i, Complex.normSq (v i)) (hqm v S hS).aemeasurable
                                                                                                          exact Filter.Eventually.of_forall fun h => ⟨(hA h _ hS).re_dotProduct_nonneg v, hbound v h _ hS⟩
        have hν (v : I → ℂ) (S : Set (T)) (hS : MeasurableSet S) : (ν v S).toReal = ∫ h, q v h S ∂μ := by change ((μ.bind (K v)) S).toReal = _
                                                                                                          rw [Measure.bind_apply hS (K v).measurable.aemeasurable]; rw [← integral_toReal ((K v).measurable_coe hS).aemeasurable (Filter.Eventually.of_forall fun h => measure_lt_top (K v h) _)]
                                                                                                          simp only [hKR v _ _ hS]
        let R (i j : I) : SignedMeasure (T) := (1 / 4 : ℝ) • ((ν (e i + e j)).toSignedMeasure - (ν (e i - e j)).toSignedMeasure)
        let ImN (i j : I) : SignedMeasure (T) := (1 / 4 : ℝ) • ((ν (e i - Complex.I • e j)).toSignedMeasure - (ν (e i + Complex.I • e j)).toSignedMeasure)
        let N (i j : I) : ComplexMeasure (T) := (R i j).toComplexMeasure (ImN i j)
        have hAi (S : Set (T)) (hS : MeasurableSet S) (i j : I) : Integrable (fun h => A h S i j) μ := by simp_rw [hpol _ _ hS i j]
                                                                                                          have hr := Complex.ofRealCLM.integrable_comp (((hqi (e i + e j) S hS).sub (hqi (e i - e j) S hS)).div_const 4)
                                                                                                          have hi := (Complex.ofRealCLM.integrable_comp (((hqi (e i - Complex.I • e j) S hS).sub (hqi (e i + Complex.I • e j) S hS)).div_const 4)).mul_const Complex.I
                                                                                                          convert! hr.add hi using 1 <;>
                                                                                                            simp only [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Pi.add_apply, Pi.sub_apply] <;> rfl
        have hN (S : Set (T)) (hS : MeasurableSet S) (i j : I) : N i j S = ∫ h, A h S i j ∂μ := by apply Complex.ext
                                                                                                   · simp only [N, SignedMeasure.toComplexMeasure_apply, Complex.ofReal_re, R, VectorMeasure.smul_apply, VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable hS, Measure.real, hν _ S hS]
                                                                                                     have ht := Complex.reCLM.integral_comp_comm (hAi S hS i j)
                                                                                                     simp only [Complex.reCLM_apply] at ht
                                                                                                     rw [← ht]
                                                                                                     simp_rw [hpol _ _ hS i j]
                                                                                                     rw [integral_div, integral_sub (hqi _ S hS) (hqi _ S hS)]
                                                                                                     ring
                                                                                                   · simp only [N, SignedMeasure.toComplexMeasure_apply, Complex.ofReal_im, ImN, VectorMeasure.smul_apply, VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable hS, Measure.real, hν _ S hS]
                                                                                                     have ht := Complex.imCLM.integral_comp_comm (hAi S hS i j)
                                                                                                     simp only [Complex.imCLM_apply] at ht
                                                                                                     rw [← ht]
                                                                                                     simp_rw [hpol _ _ hS i j]
                                                                                                     rw [integral_div, integral_sub (hqi _ S hS) (hqi _ S hS)]
                                                                                                     ring
        have hquad (S : Set (T)) (hS : MeasurableSet S) (v : I → ℂ) : star v ⬝ᵥ ((fun i j => N i j S : Matrix I I ℂ) *ᵥ v) = ((ν v S).toReal : ℂ) := by have hsum : star v ⬝ᵥ ((fun i j => N i j S : Matrix I I ℂ) *ᵥ v) = ∫ h, star v ⬝ᵥ (A h S *ᵥ v) ∂μ := by simp only [dotProduct, mulVec, Finset.mul_sum]
                                                                                                                                                                                                                                                                rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ((hAi S hS i j).mul_const _).const_mul _))]; apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                intro i _; rw [integral_finsetSum _ (fun j _ => ((hAi S hS i j).mul_const _).const_mul _)]
                                                                                                                                                                                                                                                                apply Finset.sum_congr rfl
                                                                                                                                                                                                                                                                intro j _; rw [integral_const_mul, integral_mul_const, ← hN S hS i j]
                                                                                                                                                        rw [hsum]
                                                                                                                                                        simp_rw [hreal v _ _ hS]
                                                                                                                                                        change (∫ h, Complex.ofRealCLM (q v h S) ∂μ) = _; rw [Complex.ofRealCLM.integral_comp_comm (hqi v S hS), Complex.ofRealCLM_apply, ← hν v S hS]
        have hNpos (S : Set (T)) (hS : MeasurableSet S) : Matrix.PosSemidef (fun i j => N i j S) := by apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
                                                                                                       · ext i j
                                                                                                         simp only [conjTranspose_apply, hN S hS, Complex.star_def, ← integral_conj]
                                                                                                         congr 1
                                                                                                         funext h
                                                                                                         exact congrFun (congrFun (hA h _ hS).isHermitian.eq i) j
                                                                                                       · intro v
                                                                                                         rw [hquad S hS v]
                                                                                                         exact_mod_cast ENNReal.toReal_nonneg
        let P : Kernel H T := Kernel.sum (fun i => K (e i))
        have hP (h : H) (E : Set T) (hE : MeasurableSet E) : P h E = ENNReal.ofReal (Matrix.trace (A h E)).re := by change (Kernel.sum (fun i => K (e i))) h E = _
                                                                                                                    rw [Kernel.sum_apply' _ _ hE, tsum_fintype]
                                                                                                                    simp_rw [hK _ h E hE]
                                                                                                                    have hn (i : I) (_ : i ∈ Finset.univ) : 0 ≤ (star (e i) ⬝ᵥ (A h E *ᵥ e i)).re := (hA h E hE).re_dotProduct_nonneg (e i)
                                                                                                                    rw [← ENNReal.ofReal_sum_of_nonneg hn]
                                                                                                                    congr 1
                                                                                                                    simp only [hdiag, Matrix.trace, Matrix.diag, Complex.re_sum]
        letI : IsMarkovKernel P := ⟨fun h => ⟨by simp [hP h _ MeasurableSet.univ, htrace h]⟩⟩
        let τ := μ.bind P
        letI : IsFiniteMeasure τ := by refine ⟨?_⟩
                                       change (μ.bind P) Set.univ < ∞; rw [Measure.bind_apply MeasurableSet.univ P.measurable.aemeasurable]
                                       simpa using measure_lt_top μ Set.univ
        have hmarginal : τ.map p = μ := by ext E hE
                                           rw [Measure.map_apply hp hE]; change (μ.bind P) (p ⁻¹' E) = μ E
                                           rw [Measure.bind_apply (hE.preimage hp) P.measurable.aemeasurable]
                                           have he (h : H) : P h (p ⁻¹' E) = if h ∈ E then 1 else 0 := by rw [hP h _ (hE.preimage hp), hproject h E hE]
                                                                                                          split_ifs <;> simp [htrace h]
                                           simp_rw [he]
                                           simpa [Set.indicator] using lintegral_indicator hE (fun _ : H => (1 : ℝ≥0∞))
        have hτ (S : Set (T)) (hS : MeasurableSet S) : (τ S).toReal = ∫ h, (Matrix.trace (A h S)).re ∂μ := by change ((μ.bind P) S).toReal = _
                                                                                                              rw [Measure.bind_apply hS P.measurable.aemeasurable]; rw [← integral_toReal (P.measurable_coe hS).aemeasurable (Filter.Eventually.of_forall fun h => measure_lt_top (P h) _)]
                                                                                                              apply integral_congr_ae
                                                                                                              exact Filter.Eventually.of_forall fun h => by change (P h S).toReal = (Matrix.trace (A h S)).re
                                                                                                                                                            rw [hP h _ hS, ENNReal.toReal_ofReal]; exact (Complex.nonneg_iff.mp (hA h _ hS).trace_nonneg).1
        have hNtrace (S : Set (T)) (hS : MeasurableSet S) : Matrix.trace (fun i j => N i j S : Matrix I I ℂ) = ((τ S).toReal : ℂ) := by simp only [Matrix.trace, Matrix.diag, hN S hS]
                                                                                                                                        rw [← integral_finsetSum _ (fun i _ => hAi S hS i i), hτ S hS]
                                                                                                                                        have hti : Integrable (fun h => (Matrix.trace (A h S)).re) μ := by exact Complex.reCLM.integrable_comp (integrable_finsetSum _ (fun i _ => hAi S hS i i))
                                                                                                                                        have ht := Complex.ofRealCLM.integral_comp_comm hti
                                                                                                                                        simp only [Complex.ofRealCLM_apply] at ht
                                                                                                                                        rw [← ht]
                                                                                                                                        congr 1
                                                                                                                                        funext h
                                                                                                                                        apply Complex.ext
                                                                                                                                        · simp [Matrix.trace, Complex.re_sum]
                                                                                                                                        · have hz := (Complex.nonneg_iff.mp (hA h S hS).trace_nonneg).2
                                                                                                                                          simpa only [Matrix.trace, Matrix.diag, Complex.im_sum, Complex.ofRealCLM_apply, Complex.ofReal_im] using hz.symm
        obtain ⟨τ', hτ'finite, hτ'trace, ρ, hρm, hρi, hρgood, hρcoord, _⟩ := D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.positive_history_density_from_coordinates N hNpos base hbase hbaseTrace
        have hτeq : τ' = τ := by letI := hτ'finite
                                 ext S hS
                                 apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top τ' S) (measure_ne_top τ S)).mp
                                 exact Complex.ofReal_injective ((hτ'trace S hS).symm.trans (hNtrace S hS))
        subst τ'
        exact ⟨N, P, τ, ρ, inferInstance, rfl, inferInstance, hmarginal, hNtrace, hρm, hρi, hρgood, hN, hNpos, hquad, hρcoord⟩
      have hnext (n : ℕ) (s : ActualHistory (H n) A) :
          ∃ t : ActualHistory (H (n+1)) A, t.law.map (J n).preceding = s.law ∧ (∀ E, MeasurableSet E → ∀ i j, (∫ h in E, t.density h i j ∂t.law) = ∫ h, CStarMatrix.ofMatrix.symm ((J n).operation h ((J n).embed h ⁻¹' E) (CStarMatrix.ofMatrix (s.density h))) i j ∂s.law) ∧ (∀ (σ : Matrix B B ℂ), σ.PosSemidef → Matrix.trace σ = 1 →
              ∀ f : H (n+1) → Matrix (A × B) (A × B) ℂ, Integrable f t.law →
              (∀ E, MeasurableSet E → ∀ i j, (∫ h in E, f h i j ∂t.law) = ∫ h in E, (t.density h ⊗ₖ σ) i j ∂t.law) →
              f =ᵐ[t.law] (fun h => t.density h ⊗ₖ σ)) := by
        letI := s.probability
        letI : ∀ h, MeasurableSpace ((J n).Outcome h) := (J n).outcomeMeasurable
        obtain ⟨K, hKfinite, hK, N, P, τ, ρ, hP, hτ, hτfinite, hmarg, htrace, hρm, hρi, hρstate, hcoord, hpos, hquad, hρcoord⟩ := hstep s.law s.density s.measurable_density s.state_density (J n).Outcome (J n).embed (J n).legal (J n).preceding (J n).measurable_preceding (J n).preceding_embed (J n).operation (J n).empty_operation (J n).additive_operation (J n).trace_preserving (J n).measurable_operation ρ₀ hρ₀ hρ₀trace
        have hprob : IsProbabilityMeasure τ := by constructor
                                                  have ht := congrArg (fun m : Measure (H n) => m Set.univ) hmarg
                                                  rw [Measure.map_apply (J n).measurable_preceding MeasurableSet.univ] at ht; simpa only [Set.preimage_univ, measure_univ] using ht
        let t : ActualHistory (H (n+1)) A := ⟨τ, hprob, ρ, hρm, hρi, hρstate⟩
        refine ⟨t, hmarg, ?_, ?_⟩
        · intro E hE i j
          exact (hρcoord E hE i j).trans (hcoord E hE i j)
        · intro σ hσpos hσtrace f hf hfc
          let C : (A × B) → (A × B) → ComplexMeasure (H (n+1)) := fun i j => σ i.2 j.2 • N i.1 j.1
          have hC (E : Set (H (n+1))) : (fun i j => C i j E) = (fun i j => N i j E) ⊗ₖ σ := by ext ⟨i,a⟩ ⟨j,b⟩
                                                                                               simp only [C, VectorMeasure.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
                                                                                               exact mul_comm _ _
          let M : D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.PositiveHistoryMeasure (H (n+1)) (A × B) :=
            { coordinate := C
              traceMeasure := τ
              finite_trace := hτfinite
              positive := fun E hE => by rw [hC]; exact (hpos E hE).kronecker hσpos
              trace_eq := fun E hE => by rw [hC, Matrix.trace_kronecker, htrace E hE, hσtrace, mul_one] }
          have hpi : Integrable (fun h => ρ h ⊗ₖ σ) τ := by apply Integrable.of_eval
                                                            intro ⟨i,a⟩; apply Integrable.of_eval
                                                            intro ⟨j,b⟩; exact ((hρi.eval i).eval j).mul_const (σ a b)
          have hpcoord (E : Set (H (n+1))) (hE : MeasurableSet E) (i j : A × B) : (∫ h in E, (ρ h ⊗ₖ σ) i j ∂τ) = C i j E := by
            rcases i with ⟨i,a⟩
            rcases j with ⟨j,b⟩
            change (∫ h in E, ρ h i j * σ a b ∂τ) = _; rw [integral_mul_const, hρcoord E hE i j]
            simp only [C, VectorMeasure.smul_apply, smul_eq_mul]
            exact mul_comm _ _
          obtain ⟨r, hrm, hri, hrgood, hrcoord, hrunique⟩ := D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.positive_history_density M (ρ₀ ⊗ₖ σ) (hρ₀.kronecker hσpos) (by rw [Matrix.trace_kronecker, hρ₀trace, hσtrace, one_mul])
          have hpr := hrunique (fun h => ρ h ⊗ₖ σ) hpi hpcoord
          have hfr := hrunique f hf (fun E hE i j => (hfc E hE i j).trans (hpcoord E hE i j))
          exact hfr.trans hpr.symm
      let s₀ : ActualHistory (H 0) A := ⟨Measure.dirac h₀, inferInstance, (fun _ => ρ₀), measurable_const, integrable_const _, (fun _ => ⟨hρ₀, hρ₀trace⟩)⟩
      let S : ∀ n, ActualHistory (H n) A := fun n => Nat.rec s₀ (fun n s => (hnext n s).choose) n
      have hrec (n : ℕ) : S (n+1) = (hnext n (S n)).choose := rfl
      have hmarg (n : ℕ) : (S (n+1)).law.map (J n).preceding = (S n).law := by rw [hrec]
                                                                               exact (hnext n (S n)).choose_spec.1
      have hlocal : ∀ n E, MeasurableSet E → ∀ i j, (∫ h in E, (S (n+1)).density h i j ∂(S (n+1)).law) = ∫ h, CStarMatrix.ofMatrix.symm ((J n).operation h ((J n).embed h ⁻¹' E) (CStarMatrix.ofMatrix ((S n).density h))) i j ∂(S n).law := by intro n E hE i j
                                                                                                                                                                                                                                                rw [hrec]; exact (hnext n (S n)).choose_spec.2.1 E hE i j
      have hunique (n : ℕ) (σ : Matrix B B ℂ) (hσpos : σ.PosSemidef) (hσtrace : Matrix.trace σ = 1) :
          ∀ f : H (n+1) → Matrix (A × B) (A × B) ℂ, Integrable f (S (n+1)).law →
          (∀ E, MeasurableSet E → ∀ i j, (∫ h in E, f h i j ∂(S (n+1)).law) = ∫ h in E, ((S (n+1)).density h ⊗ₖ σ) i j ∂(S (n+1)).law) →
          f =ᵐ[(S (n+1)).law] (fun h => (S (n+1)).density h ⊗ₖ σ) := by
        rw [hrec]; exact (hnext n (S n)).choose_spec.2.2 σ hσpos hσtrace
      refine ⟨S, rfl, hmarg, hlocal, ?_⟩
      intro σ hσpos hσtrace G hinit hproduct hjoint
      have hind {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (H : ℕ → Type u) [∀ n, MeasurableSpace (H n)] (μ ν : ∀ n, Measure (H n)) (hμ : ∀ n, IsFiniteMeasure (μ n)) (hν : ∀ n, IsFiniteMeasure (ν n)) (r : ∀ n, H n → Matrix A A ℂ) (R : ∀ n, H n → Matrix (A × B) (A × B) ℂ) (hr : ∀ n, Integrable (r n) (μ n)) (hR : ∀ n, Integrable (R n) (ν n)) (hrtrace : ∀ n h, Matrix.trace (r n h) = 1) (hRtrace : ∀ n h, Matrix.trace (R n h) = 1) (σ : Matrix B B ℂ) (hσtrace : Matrix.trace σ = 1) (Φ : ∀ n, H n → Set (H (n+1)) → CompletelyPositiveMap (CStarMatrix A A ℂ) (CStarMatrix A A ℂ)) (hlocal : ∀ n E, MeasurableSet E → ∀ i j, (∫ h in E, r (n+1) h i j ∂μ (n+1)) = ∫ h, CStarMatrix.ofMatrix.symm (Φ n h E (CStarMatrix.ofMatrix (r n h))) i j ∂μ n) (hunique : ∀ n, ∀ f : H (n+1) → Matrix (A × B) (A × B) ℂ, Integrable f (μ (n+1)) → (∀ E, MeasurableSet E → ∀ i j, (∫ h in E, f h i j ∂μ (n+1)) = ∫ h in E, (r (n+1) h ⊗ₖ σ) i j ∂μ (n+1)) → f =ᵐ[μ (n+1)] (fun h => r (n+1) h ⊗ₖ σ)) (M : ℕ) (L : ∀ n, H n → Set (H (n+1)) → Matrix (A × B) (A × B) ℂ → Matrix (A × B) (A × B) ℂ) (hcompat : ∀ n h E X, L n h E (X ⊗ₖ σ) = CStarMatrix.ofMatrix.symm (Φ n h E (CStarMatrix.ofMatrix X)) ⊗ₖ σ) (hjoint : ∀ n, n < M → ∀ E, MeasurableSet E → ∀ i j, (∫ h in E, R (n+1) h i j ∂ν (n+1)) = ∫ h, L n h E (R n h) i j ∂ν n) (hinit : ν 0 = μ 0) (hproduct : R 0 =ᵐ[μ 0] (fun h => r 0 h ⊗ₖ σ)) :
          ∀ n, n ≤ M → ν n = μ n ∧ R n =ᵐ[μ n] (fun h => r n h ⊗ₖ σ) := by
        classical
        intro n
        induction n with
        | zero => intro hn; exact ⟨hinit, hproduct⟩
        | succ n ih =>
          intro hn
          have hnM : n < M := by omega
          have ih := ih (Nat.le_of_succ_le hn)
          letI := hμ n
          letI := hν n
          letI := hμ (n+1)
          letI := hν (n+1)
          have hevent (E : Set (H (n+1))) (hE : MeasurableSet E) (i j : A) (a b : B) : (∫ h in E, R (n+1) h (i,a) (j,b) ∂ν (n+1)) = (∫ h in E, r (n+1) h i j ∂μ (n+1)) * σ a b := by rw [hjoint (n) hnM E hE, ih.1]
                                                                                                                                                                                     calc
                                                                                                                                                                                       _ = ∫ h, CStarMatrix.ofMatrix.symm (Φ n h E (CStarMatrix.ofMatrix (r n h))) i j * σ a b ∂μ n := by apply integral_congr_ae
                                                                                                                                                                                                                                                                                          filter_upwards [ih.2] with h hh
                                                                                                                                                                                                                                                                                          rw [hh, hcompat]; rfl
                                                                                                                                                                                       _ = (∫ h, CStarMatrix.ofMatrix.symm (Φ n h E (CStarMatrix.ofMatrix (r n h))) i j ∂μ n) * σ a b := integral_mul_const _ _
                                                                                                                                                                                       _ = _ := by rw [hlocal n E hE]
          have htraceR (E : Set (H (n+1))) (hE : MeasurableSet E) : Matrix.trace (fun i j => ∫ h in E, R (n+1) h i j ∂ν (n+1)) = ((ν (n+1) E).toReal : ℂ) := by simp only [Matrix.trace, Matrix.diag]
                                                                                                                                                                rw [← integral_finsetSum _ (fun i _ => (((hR (n+1)).eval i).eval i).integrableOn)]; change (∫ h in E, Matrix.trace (R (n+1) h) ∂ν (n+1)) = _
                                                                                                                                                                simp [hRtrace, Measure.real]
          have htracer (E : Set (H (n+1))) (hE : MeasurableSet E) : Matrix.trace (fun i j => ∫ h in E, r (n+1) h i j ∂μ (n+1)) = ((μ (n+1) E).toReal : ℂ) := by simp only [Matrix.trace, Matrix.diag]
                                                                                                                                                                rw [← integral_finsetSum _ (fun i _ => (((hr (n+1)).eval i).eval i).integrableOn)]; change (∫ h in E, Matrix.trace (r (n+1) h) ∂μ (n+1)) = _
                                                                                                                                                                simp [hrtrace, Measure.real]
          have hmeasure : ν (n+1) = μ (n+1) := by ext E hE
                                                  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (ν (n+1)) E) (measure_ne_top (μ (n+1)) E)).mp
                                                  apply Complex.ofReal_injective
                                                  rw [← htraceR E hE, ← htracer E hE]
                                                  have he : (fun i j => ∫ h in E, R (n+1) h i j ∂ν (n+1)) = (fun i j => ∫ h in E, r (n+1) h i j ∂μ (n+1)) ⊗ₖ σ := by ext ⟨i,a⟩ ⟨j,b⟩
                                                                                                                                                                     exact hevent E hE i j a b
                                                  rw [he, Matrix.trace_kronecker, hσtrace, mul_one]
          refine ⟨hmeasure, ?_⟩
          have hRa : Integrable (R (n+1)) (μ (n+1)) := by rw [← hmeasure]
                                                          exact hR (n+1)
          apply hunique n (R (n+1)) hRa
          intro E hE ⟨i,a⟩ ⟨j,b⟩; change (∫ h in E, R (n+1) h (i,a) (j,b) ∂μ (n+1)) = ∫ h in E, r (n+1) h i j * σ a b ∂μ (n+1)
          rw [integral_mul_const]
          simpa only [hmeasure] using hevent E hE i j a b
      have hp : (G 0).density =ᵐ[(S 0).law] (fun h => (S 0).density h ⊗ₖ σ) := by change (G 0).density =ᵐ[Measure.dirac h₀] (fun _ => ρ₀ ⊗ₖ σ)
                                                                                  rw [← hinit]
                                                                                  exact hproduct
      exact hind H (fun n => (S n).law) (fun n => (G n).law) (fun n => by letI := (S n).probability; infer_instance) (fun n => by letI := (G n).probability; infer_instance) (fun n => (S n).density) (fun n => (G n).density) (fun n => (S n).integrable_density) (fun n => (G n).integrable_density) (fun n h => ((S n).state_density h).2) (fun n h => ((G n).state_density h).2) σ hσtrace (fun n h E => (J n).operation h ((J n).embed h ⁻¹' E)) hlocal (fun n => hunique n σ hσpos hσtrace) M L (hcompat σ) hjoint hinit hp
    obtain ⟨S, hSinit, hmarg, hlocal, hlaw⟩ := hwhole H K (completedStoppedStep P H_A) hcompat h₀ ρ₀ hρ₀ hρ₀trace N
    have hphysicalCompleted (σ : DensityState (Fin e)) (n : ℕ) (hn : n < N) (E : Set (H (n+1))) (hE : MeasurableSet E) (i j : A × Fin e) : (∫ h in E, (G σ (n+1)).density h i j ∂(G σ (n+1)).law) = ∫ h, completedStoppedStep P H_A n h E ((G σ n).density h) i j ∂(G σ n).law := by rw [hphysical σ n hn E hE]
                                                                                                                                                                                                                                                                                     apply integral_congr_ae
                                                                                                                                                                                                                                                                                     filter_upwards [hnormalized σ n hn] with h hn
                                                                                                                                                                                                                                                                                     by_cases hs : h ∈ P.stop n
                                                                                                                                                                                                                                                                                     · simp only [actualStoppedStep, completedStoppedStep, hs, if_pos hs, Set.mem_union, true_or, if_true]
                                                                                                                                                                                                                                                                                     · have hd : h ∈ normalizationDomain (P.stage n) := (hdomain (P.stage n)).2 h |>.mpr (hn hs)
                                                                                                                                                                                                                                                                                       simp only [actualStoppedStep, completedStoppedStep, if_neg hs, Set.mem_union, hs, false_or, Set.mem_compl_iff, hd, not_true_eq_false, if_false]
    have hequal (σ : DensityState (Fin e)) (n : ℕ) (hn : n ≤ N) : (G σ n).law = (S n).law := by have hσ : (CStarMatrix.ofMatrix.symm σ.1).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
                                                                                                exact (hlaw (CStarMatrix.ofMatrix.symm σ.1) hσ σ.2.2 (G σ) (hinit σ) (hproduct σ) (hphysicalCompleted σ) n hn).1
    have hstoppedMass (n : ℕ) (hn : n < N) (F : Set (ℕ × D)) (hF : MeasurableSet F) : (S (n+1)).law ((P.stage n).preceding ⁻¹' P.stop n ∩ P.record (n+1) ⁻¹' F) = (S n).law (P.stop n ∩ P.record n ⁻¹' F) := by let E := (P.stage n).preceding ⁻¹' P.stop n ∩ P.record (n+1) ⁻¹' F
                                                                                                                                                                                                                let C := P.stop n ∩ P.record n ⁻¹' F
                                                                                                                                                                                                                have hE : MeasurableSet E := ((P.measurable_stop n).preimage (P.stage n).measurable_preceding).inter (hF.preimage (P.measurable_record (n+1)))
                                                                                                                                                                                                                have hC : MeasurableSet C := (P.measurable_stop n).inter (hF.preimage (P.measurable_record n))
                                                                                                                                                                                                                let σref := gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)
                                                                                                                                                                                                                have hgood : ∀ᵐ h ∂(S n).law, h ∈ P.stop n ∨ h ∈ normalizationDomain (P.stage n) := by rw [← hequal σref n hn.le]
                                                                                                                                                                                                                                                                                                       filter_upwards [hnormalized σref n hn] with h hh
                                                                                                                                                                                                                                                                                                       by_cases hs : h ∈ P.stop n
                                                                                                                                                                                                                                                                                                       · exact Or.inl hs
                                                                                                                                                                                                                                                                                                       · exact Or.inr (((hdomain (P.stage n)).2 h).mpr (hh hs))
                                                                                                                                                                                                                have hpoint (h : H n) (hh : h ∈ P.stop n ∨ h ∈ normalizationDomain (P.stage n)) : CStarMatrix.ofMatrix.symm ((K n).operation h ((K n).embed h ⁻¹' E) (CStarMatrix.ofMatrix ((S n).density h))) = if h ∈ C then (S n).density h else 0 := by rw [hK]
                                                                                                                                                                                                                                                                                                                                                                                                                                                            dsimp only [stop']
                                                                                                                                                                                                                                                                                                                                                                                                                                                            by_cases hs : h ∈ P.stop n
                                                                                                                                                                                                                                                                                                                                                                                                                                                            · have hs' : h ∈ P.stop n ∪ (normalizationDomain (P.stage n))ᶜ := Or.inl hs
                                                                                                                                                                                                                                                                                                                                                                                                                                                              have hc : P.cemetery n h ∈ E ↔ h ∈ C := by simp only [E, C, Set.mem_inter_iff, Set.mem_preimage, P.preceding_cemetery, P.stopped_record n h hs]
                                                                                                                                                                                                                                                                                                                                                                                                                                                              by_cases hhC : h ∈ C
                                                                                                                                                                                                                                                                                                                                                                                                                                                              · simp only [stop', if_pos hs', if_pos (hc.mpr hhC), if_pos hhC]
                                                                                                                                                                                                                                                                                                                                                                                                                                                              · simp only [stop', if_pos hs', if_neg (fun he => hhC (hc.mp he)), if_neg hhC]
                                                                                                                                                                                                                                                                                                                                                                                                                                                            · have hd := hh.resolve_left hs
                                                                                                                                                                                                                                                                                                                                                                                                                                                              have hs' : h ∉ P.stop n ∪ (normalizationDomain (P.stage n))ᶜ := fun he => he.elim hs (fun he => he hd)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              have hempty : (P.stage n).embed h ⁻¹' E = ∅ := by ext o
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                simp only [E, Set.mem_preimage, Set.mem_inter_iff, (P.stage n).preceding_embed, hs, false_and, Set.mem_empty_iff_false]
                                                                                                                                                                                                                                                                                                                                                                                                                                                              have hnC : h ∉ C := fun hc => hs hc.1
                                                                                                                                                                                                                                                                                                                                                                                                                                                              rw [if_neg hs', hempty, (P.stage n).empty_operation]
                                                                                                                                                                                                                                                                                                                                                                                                                                                              simp only [if_neg hnC]
                                                                                                                                                                                                                have hevent (i j : A) : (∫ h in E, (S (n+1)).density h i j ∂(S (n+1)).law) = ∫ h in C, (S n).density h i j ∂(S n).law := by rw [hlocal n E hE]
                                                                                                                                                                                                                                                                                                                                            calc
                                                                                                                                                                                                                                                                                                                                              _ = ∫ h, C.indicator (fun h => (S n).density h i j) h ∂(S n).law := by apply integral_congr_ae
                                                                                                                                                                                                                                                                                                                                                                                                                     filter_upwards [hgood] with h hh
                                                                                                                                                                                                                                                                                                                                                                                                                     rw [hpoint h hh]
                                                                                                                                                                                                                                                                                                                                                                                                                     by_cases hc : h ∈ C
                                                                                                                                                                                                                                                                                                                                                                                                                     · simp only [if_pos hc, Set.indicator_of_mem hc]
                                                                                                                                                                                                                                                                                                                                                                                                                     · simp only [if_neg hc, Matrix.zero_apply, Set.indicator_of_notMem hc]
                                                                                                                                                                                                                                                                                                                                              _ = _ := integral_indicator hC
                                                                                                                                                                                                                have htrace {T : Type u} [MeasurableSpace T] (s : ActualHistory T A) (E : Set T) (hE : MeasurableSet E) : Matrix.trace (fun i j => ∫ h in E, s.density h i j ∂s.law) = ((s.law E).toReal : ℂ) := by letI := s.probability
                                                                                                                                                                                                                                                                                                                                                                                                                    simp only [Matrix.trace, Matrix.diag]
                                                                                                                                                                                                                                                                                                                                                                                                                    rw [← integral_finsetSum _ (fun i _ => ((s.integrable_density.eval i).eval i).integrableOn)]
                                                                                                                                                                                                                                                                                                                                                                                                                    change (∫ h in E, Matrix.trace (s.density h) ∂s.law) = _
                                                                                                                                                                                                                                                                                                                                                                                                                    simp [fun h => (s.state_density h).2, Measure.real]
                                                                                                                                                                                                                letI := (S n).probability
                                                                                                                                                                                                                letI := (S (n+1)).probability
                                                                                                                                                                                                                apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (S (n+1)).law E) (measure_ne_top (S n).law C)).mp
                                                                                                                                                                                                                apply Complex.ofReal_injective
                                                                                                                                                                                                                rw [← htrace (S (n+1)) E hE, ← htrace (S n) C hC]
                                                                                                                                                                                                                congr 1
                                                                                                                                                                                                                ext i j
                                                                                                                                                                                                                exact hevent i j
    let μ := (S N).law
    have houtput (σ : DensityState (Fin e)) : (G σ N).law.map (P.record N) = μ.map (P.record N)  := by rw [hequal σ N le_rfl]
    refine ⟨μ, (S N).probability, (fun σ => hequal σ N le_rfl), houtput, ?_, ?_⟩
    · intro σ n hn F hF
      rw [hequal σ (n+1) (by omega), hequal σ n hn.le]
      exact hstoppedMass n hn F hF
    · letI := (S N).probability
      let outputLaw := μ.map (P.record N)
      haveI : IsProbabilityMeasure outputLaw := by constructor
                                                   rw [Measure.map_apply (P.measurable_record N) MeasurableSet.univ]
                                                   simp
      simp_rw [houtput]
      have hendpoints (e : ℕ) [NeZero e] (β : ℝ) (hβ : 0 < β) :
          let ω := gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)
          let θ := fun σ : DensityState (Fin e) => quantumRelativeEntropy σ ω / β
          (∀ σ, θ σ ∈ Set.Icc 0 (Real.log e / β)) ∧ θ ω = 0 ∧ θ (pointerState (0 : Fin e)) = Real.log e / β := by
        dsimp only
        let ω := gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)
        refine ⟨?_, ?_, ?_⟩
        · intro σ
          have h := entropy_freedom_segment σ
          change 0 ≤ vonNeumannEntropy σ ∧ 0 ≤ quantumRelativeEntropy σ ω ∧ vonNeumannEntropy σ + quantumRelativeEntropy σ ω = Real.log e at h
          exact ⟨div_nonneg h.2.1 hβ.le, (div_le_div_of_nonneg_right (by linarith [h.1, h.2.2]) hβ.le)⟩
        · have hs : quantumRelativeEntropy ω ω = 0 := by simp only [quantumRelativeEntropy, sub_self, mul_zero]
                                                         change (Matrix.trace (0 : Matrix (Fin e) (Fin e) ℂ)).re = 0
                                                         simp
          change quantumRelativeEntropy ω ω / β = 0
          rw [hs, zero_div]
        · have hp := entropy_uniform_identity (pointerState (0 : Fin e))
          rw [entropy_pointerState] at hp
          simpa only [zero_add, Fintype.card_fin] using congrArg (fun x : ℝ => x / β) hp
      have hminimax {H : Type u} {S : Type} [MeasurableSpace H] (μ : Measure H) [IsProbabilityMeasure μ] (θ : S → ℝ) (L : ℝ) (hL : 0 ≤ L) (hθ : ∀ s, θ s ∈ Set.Icc 0 L) (s₀ s₁ : S) (h₀ : θ s₀ = 0) (h₁ : θ s₁ = L) : (⨅ κ : RealOutput H, ⨆ s : S, ∫⁻ z : ℝ, ENNReal.ofReal |z - θ s| ∂(μ.bind κ.kernel)) = ENNReal.ofReal (L / 2) := by have hlower (κ : RealOutput H) : ENNReal.ofReal (L / 2) ≤ ⨆ s : S, ∫⁻ z : ℝ, ENNReal.ofReal |z - θ s| ∂(μ.bind κ.kernel) := by
                                                                                                                                                                                                                                                                                                                                            letI := κ.markov
                                                                                                                                                                                                                                                                                                                                            let ν := μ.bind κ.kernel
                                                                                                                                                                                                                                                                                                                                            haveI : IsProbabilityMeasure ν := by constructor
                                                                                                                                                                                                                                                                                                                                                                                 change (μ.bind κ.kernel) Set.univ = 1
                                                                                                                                                                                                                                                                                                                                                                                 rw [Measure.bind_apply MeasurableSet.univ κ.kernel.measurable.aemeasurable]
                                                                                                                                                                                                                                                                                                                                                                                 simp
                                                                                                                                                                                                                                                                                                                                            let a := ∫⁻ z : ℝ, ENNReal.ofReal |z| ∂ν
                                                                                                                                                                                                                                                                                                                                            let b := ∫⁻ z : ℝ, ENNReal.ofReal |z - L| ∂ν
                                                                                                                                                                                                                                                                                                                                            have hab : ENNReal.ofReal L ≤ a + b := by have hpoint (z : ℝ) : L ≤ |z| + |z - L| := by
                                                                                                                                                                                                                                                                                                                                                                                        have h := abs_sub_le z 0 (z - L)
                                                                                                                                                                                                                                                                                                                                                                                        simpa only [sub_sub_cancel, sub_zero, zero_sub, abs_of_nonneg hL, abs_neg] using h
                                                                                                                                                                                                                                                                                                                                                                                      calc
                                                                                                                                                                                                                                                                                                                                                                                        ENNReal.ofReal L = ∫⁻ _ : ℝ, ENNReal.ofReal L ∂ν := by simp
                                                                                                                                                                                                                                                                                                                                                                                        _ ≤ ∫⁻ z : ℝ, ENNReal.ofReal |z| + ENNReal.ofReal |z - L| ∂ν := by apply lintegral_mono
                                                                                                                                                                                                                                                                                                                                                                                                                                                           intro z
                                                                                                                                                                                                                                                                                                                                                                                                                                                           change ENNReal.ofReal L ≤ ENNReal.ofReal |z| + ENNReal.ofReal |z - L|
                                                                                                                                                                                                                                                                                                                                                                                                                                                           rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
                                                                                                                                                                                                                                                                                                                                                                                                                                                           exact ENNReal.ofReal_le_ofReal (hpoint z)
                                                                                                                                                                                                                                                                                                                                                                                        _ = a + b := lintegral_add_left (ENNReal.measurable_ofReal.comp (continuous_abs : Continuous (fun x : ℝ => |x|)).measurable) _
                                                                                                                                                                                                                                                                                                                                            have hmax : ENNReal.ofReal (L / 2) ≤ max a b := by rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                                                                                                                                                                                                                                                                                                                                                                                               apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
                                                                                                                                                                                                                                                                                                                                                                                               exact hab.trans (by simpa only [mul_two] using add_le_add (le_max_left a b) (le_max_right a b))
                                                                                                                                                                                                                                                                                                                                            apply hmax.trans
                                                                                                                                                                                                                                                                                                                                            apply max_le
                                                                                                                                                                                                                                                                                                                                            · simpa only [a, ν, h₀, sub_zero] using (le_iSup (fun s : S => ∫⁻ z : ℝ, ENNReal.ofReal |z - θ s| ∂(μ.bind κ.kernel)) s₀)
                                                                                                                                                                                                                                                                                                                                            · simpa only [b, ν, h₁] using (le_iSup (fun s : S => ∫⁻ z : ℝ, ENNReal.ofReal |z - θ s| ∂(μ.bind κ.kernel)) s₁)
                                                                                                                                                                                                                                                                                                                                          apply le_antisymm
                                                                                                                                                                                                                                                                                                                                          · let κ : RealOutput H := ⟨Kernel.const H (Measure.dirac (L/2)), inferInstance⟩
                                                                                                                                                                                                                                                                                                                                            refine (iInf_le _ κ).trans (iSup_le fun s => ?_)
                                                                                                                                                                                                                                                                                                                                            change (∫⁻ z : ℝ, ENNReal.ofReal |z - θ s| ∂(μ.bind (fun _ => Measure.dirac (L/2)))) ≤ _
                                                                                                                                                                                                                                                                                                                                            rw [Measure.bind_const, measure_univ, one_smul, lintegral_dirac]
                                                                                                                                                                                                                                                                                                                                            apply ENNReal.ofReal_le_ofReal
                                                                                                                                                                                                                                                                                                                                            apply abs_le.mpr
                                                                                                                                                                                                                                                                                                                                            constructor <;> linarith [(hθ s).1, (hθ s).2]
                                                                                                                                                                                                                                                                                                                                          · exact le_iInf hlower
      let ω := gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)
      let θ := fun σ : DensityState (Fin e) => quantumRelativeEntropy σ ω / β
      let L := Real.log e / β
      obtain ⟨hrange, hzero, hpure⟩ := hendpoints e β hβ
      have hL : 0 ≤ L := div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ e by omega))) hβ.le
      have hm := hminimax outputLaw θ L hL hrange ω (pointerState (0 : Fin e)) hzero hpure
      have hhalf : L / 2 = Real.log e / (2 * β) := by dsimp only [L]
                                                      rw [div_div]
                                                      congr 1
                                                      exact mul_comm _ _
      rw [hhalf] at hm
      exact hm
  let ix := historyIndex N
  let H := fun n => F (ix n)
  letI : ∀ n, MeasurableSpace (H n) := fun n => inferInstanceAs (MeasurableSpace (F (ix n)))
  obtain ⟨Q, hstage, hstop, htime, hcem, hrecord⟩ := hpadding N F D A P.record P.measurable_record P.stop P.measurable_stop P.stage P.time P.measurable_time P.cemetery P.measurable_cemetery P.preceding_cemetery P.stopped_cemetery P.stopped_record P.active_length
  let G' (σ : DensityState (Fin e)) (n : ℕ) : ActualHistory (H n) (A × Fin e) := G σ (ix n)
  have hstep (n : ℕ) (hn : n < N) (h : H n) (E : Set (H (n+1))) (X : Matrix (A × Fin e) (A × Fin e) ℂ) : actualStoppedStep Q H_A n h E X = actualFiniteStep P H_A n hn h E X := by simp only [actualStoppedStep, actualFiniteStep, hstop n hn, htime n hn, hcem n hn]
                                                                                                                                                                                   rw [hstage n hn]
  have hn' (σ : DensityState (Fin e)) (n : ℕ) (hn : n < N) :
      ∀ᵐ h ∂(G' σ n).law, h ∉ Q.stop n → ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm ((Q.stage n).operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X := by
    rw [hstage n hn, hstop n hn]
    exact hnormalized σ n hn
  have hp' (σ : DensityState (Fin e)) (n : ℕ) (hn : n < N) (E : Set (H (n+1))) (hE : MeasurableSet E) (i j : A × Fin e) : (∫ h in E, (G' σ (n+1)).density h i j ∂(G' σ (n+1)).law) = ∫ h, actualStoppedStep Q H_A n h E ((G' σ n).density h) i j ∂(G' σ n).law := by simpa only [G', hstep n hn] using hphysical σ n hn E hE i j
  have result := hbounded e he β hβ H D Q H_A hH_A h₀ ρ₀ hρ₀ hρ₀trace G' hinit hproduct N hn' hp'
  obtain ⟨μ, hμ, hlaw, hout, hmass, hrisk⟩ := result
  refine ⟨μ, hμ, hlaw, ?_, ?_, ?_⟩
  · simpa only [G', H, ix, historyIndex, hrecord] using hout
  · intro σ n hn E hE
    have hh := hmass σ n hn E hE
    rw [hstage n hn, hstop n hn, hrecord (n+1), hrecord n] at hh
    exact hh
  · have htarget (σ : DensityState (Fin e)) : quantumRelativeEntropy σ (gibbsState (0 : CStarMatrix (Fin e) (Fin e) ℂ) (IsSelfAdjoint.zero _)) / β = (Real.log e - vonNeumannEntropy σ) / β := by have ht := entropy_uniform_identity σ
                                                                                                                                                                                                  simp only [Fintype.card_fin] at ht
                                                                                                                                                                                                  congr 1
                                                                                                                                                                                                  linarith
    simpa only [G', H, ix, historyIndex, hrecord, htarget] using hrisk
#print axioms visible_adaptive_record_law_and_absolute_minimax
end D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
