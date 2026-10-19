import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily



open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily



open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ θ => θ) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def sourceLaw (r : Realization observationSignature) : Prop := (∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (P : List Label) (h : List Color) (hP : LegalWord .G0 s P)
    (hPlen : P.length = h.length)
    (R : Bool → List Label) (W : Bool → List Color)
    (hR : ∀ i, LegalWord s s (R i)) (hlen : ∀ i, (R i).length = (W i).length)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (R i) (W i)),
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ zs : List Bool,
        OperationRecord o (r.readout () () θ) .closed
          (address ((P ++ choiceBlocks R zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks R zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length + p) = observe o (coordinate w p) 0)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law := sourceLaw

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hsupp : ∀ z ∈ Set.Icc (-1 : ℝ) phi, InSupport .G0 z := by
    intro z hz
    simpa only [Set.mem_Icc, InSupport, supportUpper] using hz
  have hinv : ∀ (i : Bool) (z : ℝ), (-1 : ℝ) ≤ z → z ≤ phi →
      (-1 : ℝ) ≤ compose ([] : List Label) z ∧ compose ([] : List Label) z ≤ phi := by
    intro i z hlo hhi
    simpa only [compose] using And.intro hlo hhi
  have hcert : EndpointCertificate 0 (-1 : ℝ) phi [] [] := by
    intro r hr
    simp at hr
  have bad := h (fun _ => false) 0 (by norm_num) .G0 [] [] (by rfl) (by rfl)
    (fun _ => []) (fun _ => []) (by intro i; rfl) (by intro i; rfl)
    (-1) phi (by linarith [tail_arithmetic.2.2.2.2.2]) hsupp hinv hcert
    (by intro i; exact hcert)
  obtain ⟨e, w, hw, hlo, hhi, hall⟩ := bad
  obtain ⟨record, hfinite, hfuture⟩ := hall []
  obtain ⟨x, hx, err, herr, hread⟩ := record
  have impossible := herr 0
  change |err 0| ≤ (-1 : ℝ) at impossible
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_finite_tail_all_histories) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_finite_tail_all_histories, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ θ => θ) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def sourceLaw (r : Realization observationSignature) : Prop := (∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (A : List Label) (cs : List Color) (hlen : A.length = cs.length)
    (hA : LegalWord .G0 s A)
    (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hp0 : path 0 = s)
    (hedge : ∀ p, nextGuard (path p) (tail p) = some (path (p+1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (tail p) (x (p+1)))
    (supply : BlockSupply o θ false A cs (x 0)),
    ∃ beta X, OperationOmega beta X ∧
      (∀ p (hp : p < A.length), beta p = A[p]) ∧
      (∀ p, beta (A.length+p) = tail p) ∧
      (∀ p, X (A.length+p) = x p) ∧
      OperationRecord o (r.readout () () θ) .closed beta (recordWithOmegaTail o cs x))

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law := sourceLaw

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hsupp : ∀ (p : ℕ), InSupport .G0 (0 : ℝ) := by
    intro p
    simpa only [InSupport, supportUpper] using
      (show (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ phi from
        ⟨by norm_num, by linarith [tail_arithmetic.2.2.2.2.2]⟩)
  have supply : BlockSupply (fun _ => false) 0 false [] [] 0 := by
    intro p hp
    simp at hp
  have bad := h (fun _ => false) 0 (by norm_num) .G0 [] [] (by rfl) (by rfl)
    (fun _ => .L0) (fun _ => 0) (fun _ => .G0) (by rfl)
    (by intro p; rfl) hsupp (by intro p; simp [branch, shift]) supply
  obtain ⟨beta, X, hOmega, hprefix, htail, hcoords, record⟩ := bad
  obtain ⟨xx, hxx, err, herr, hread⟩ := record
  have impossible := herr 0
  change |err 0| ≤ (-1 : ℝ) at impossible
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.actual_omega_prefix_record) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.actual_omega_prefix_record, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ θ => θ) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def sourceLaw (r : Realization observationSignature) : Prop := (∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length)
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s Q V h W)
      else y ∈ CompetingT o θ s Q V h W),
    ∃ (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧
      (∀ p, nextGuard (path p) (tail p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (tail p) (x (p+1))) ∧
      (∀ n, (compose V)^[n] (x 0) ∈ CompetingT o θ s Q V h W) ∧
      ∀ zs : List Bool, ∃ beta X, OperationOmega beta X ∧
        (∀ p (hp : p < (Q ++ choiceBlocks (fun _ => V) zs).length),
          beta p = (Q ++ choiceBlocks (fun _ => V) zs)[p]) ∧
        (∀ p, beta ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = tail p) ∧
        (∀ p, X ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = x p) ∧
        OperationRecord o (r.readout () () θ) .closed beta
          (recordWithOmegaTail o (h ++ choiceBlocks W zs) x))

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law := sourceLaw

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hg : 0 < g := tail_arithmetic.2.2.2.1
  have hq : LegalWord .G0 .G0 ([] : List Label) := by rfl
  have hv : LegalWord .G0 .G0 ([.L0] : List Label) := by rfl
  have hW : ∀ i, ([.L0] : List Label).length = ((fun _ : Bool => [(1 : Color)]) i).length := by
    intro i
    rfl
  have hmember : (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [.L0] []
      (fun _ => [(1 : Color)]) := by
    apply (competingT_mem_actual (fun _ => false) 0 .G0 [] [.L0] []
      (fun _ => [(1 : Color)]) hq hv 0).2
    refine ⟨?_, ?_, ?_⟩
    · simpa only [InSupport, supportUpper] using
        (show (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ phi from
          ⟨by norm_num, by linarith [tail_arithmetic.2.2.2.2.2]⟩)
    · intro r hr
      simp at hr
    · intro i r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      have hz : InSupport .G0 (0 : ℝ) := by
        simpa only [InSupport, supportUpper] using
          (show (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ phi from
            ⟨by norm_num, by linarith [tail_arithmetic.2.2.2.2.2]⟩)
      have owned : OwnedColor (fun _ => false) 0 (1 : Color) 0 := by
        apply (owned_color_error (fun _ => false) 0 (1 : Color) 0 hz).mpr
        refine ⟨0, by norm_num, ?_⟩
        have hcut1 : cut 1 < (0 : ℝ) := by
          norm_num [cut, lam, T2, g]
          nlinarith [tail_arithmetic.2, tail_arithmetic.2.2]
        have hcut2 : (0 : ℝ) < cut 2 := by
          norm_num [cut, lam, T2, g]
          nlinarith [tail_arithmetic.1, tail_arithmetic.2, tail_arithmetic.2.2]
        have hphi0 : (0 : ℝ) ≤ phi := by
          linarith [tail_arithmetic.2.2.2.2.2]
        have hn1 : ¬ (0 : ℝ) < cut 1 := not_lt_of_ge hcut1.le
        have hne1 : (0 : ℝ) ≠ cut 1 := ne_of_gt hcut1
        simp [observe, clip, readout, hn1, hne1, hcut2, hphi0]
      rcases (owned_color_error (fun _ => false) 0 (1 : Color) 0 hz).mp owned with
        ⟨e, he, hread⟩
      refine ⟨e, he, ?_⟩
      simpa [compose, List.drop_zero, List.getElem_cons_zero, branch, shift] using hread
  have hfeasible : (if 0 < (-g : ℝ) then
      (CompetingT (fun _ => false) 0 .G0 [] [.L0] [] (fun _ => [(1 : Color)] )).Nonempty ∧
        (0 : ℝ) ∈ closure (CompetingT (fun _ => false) 0 .G0 [] [.L0] [] (fun _ => [(1 : Color)]))
      else (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [.L0] [] (fun _ => [(1 : Color)])) := by
    rw [if_neg (by linarith)]
    exact hmember
  have bad := h (fun _ => false) 0 (by norm_num) .G0 [] [.L0] []
    (fun _ => [(1 : Color)]) hq hv (by rfl) hW (-g) 0
    (by linarith [tail_arithmetic.2.2.2.2.1]) (by linarith) (by linarith)
    (by simp) (by simp [compose, branch, shift]) hfeasible
  obtain ⟨tail, x, path, hp0, hedge, hsupp, hrec, horbit, hall⟩ := bad
  obtain ⟨beta, X, hOmega, hprefix, htail, hcoords, record⟩ := hall []
  obtain ⟨xx, hxx, err, herr, hread⟩ := record
  have impossible := herr 0
  change |err 0| ≤ (-1 : ℝ) at impossible
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_omega_tail_all_histories) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_omega_tail_all_histories, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80
