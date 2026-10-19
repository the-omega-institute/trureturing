import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ x => x^2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := r.readout () () t = 1-t ∧ 0<t ∧ t<1 ∧ 0<g ∧ g<1 ∧ 1<phi

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq : (0 : ℝ) = 1-t := h.1
  have lt := h.2.2.1
  linarith

def evidence : Registration sourceArena (type_of% @tail_arithmetic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tail_arithmetic, rejected, rejected_law⟩
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
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Color
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ c => cut c.val) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (c : Color),
      -1 ≤ r.readout () () c ∧
      cut c.val < cut (c.val + 1) ∧
      cut (c.val + 1) ≤ phi

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h (0 : Color)).1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cut_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cut_bounds, rejected, rejected_law⟩
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
    refine ⟨(), (0 : Color), (1 : Color), ?_⟩
    exact ne_of_lt (cut_bounds (0 : Color)).2.1

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ z x => z - x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (z : ℝ) (hz : InSupport s z)
    (ε : ℝ) (hε : 0 < ε),
    ∃ (e : Guard) (w : List Label),
      LegalWord s e w ∧ |r.readout () z (coordinate w 0)| < ε

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have supported : InSupport .G0 0 := by
    constructor
    · norm_num
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le
  obtain ⟨e, w, _, impossible⟩ := h .G0 0 supported 1 (by norm_num)
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_approximation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_approximation, rejected, rejected_law⟩
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
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (List Label) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ w x => compose w x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (w : List Label) (lo hi x left right : ℝ)
    (hxlo : lo < x) (hxhi : x < hi)
    (hlo : left ≤ compose w lo ∧ compose w lo ≤ right)
    (hhi : left ≤ compose w hi ∧ compose w hi ≤ right),
    left < r.readout () w x ∧ compose w x < right

theorem source_bridge : (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside) ↔
    sourceArena.Law actual := Iff.rfl

theorem positive_law : sourceArena.Law actual := @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h [] (-1) 1 0 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num [compose]) (by norm_num [compose])).1
  exact (lt_irrefl (-1 : ℝ)) impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨[], 0, 1, ?_⟩
  norm_num [actual, realize, compose]

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Label) (fun _ => ℝ → ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ l => branch l) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)

/-- The actual branch functions distinguish two legal label states at zero. -/
theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), Label.L0, Label.L2, ?_⟩
  intro heq
  have h := congrFun heq (0 : ℝ)
  norm_num [actual, realize, branch, shift] at h

/-- Supported zero supplies an inhabited input, without restricting the Law. -/
theorem zero_supported : InSupport .G0 (0 : ℝ) := by
  exact ⟨by norm_num, (by norm_num : (0 : ℝ) ≤ 1).trans
    tail_arithmetic.2.2.2.2.2.le⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (z : ℝ) (hz : InSupport s z),
    ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧ x 0 = z ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = r.readout () () (a p) (x (p + 1)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨a, x, path, hpath0, hx0, hedges, hsupp, hrec⟩ :=
    h .G0 0 LiteralBranchReadout.zero_supported
  have h := hrec 0
  change x 0 = (1 : ℝ) at h
  rw [hx0] at h
  norm_num at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.lawful_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.lawful_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (lo hi : ℝ) (hlt : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z),
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      OperationFiniteSource (address w) ∧
      ∃ path : ℕ → Guard, path 0 = s ∧
        (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (coordinate w p)) ∧
        (∀ p, coordinate w p = r.readout () () (address w p) (coordinate w (p + 1)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hsupport : ∀ z ∈ Set.Icc (-1 : ℝ) 0, InSupport .G0 z := by
    intro z hz
    exact ⟨hz.1, hz.2.trans LiteralBranchReadout.zero_supported.2⟩
  obtain ⟨e, w, hw, hlo, hhi, hfinite, path, hpath0, hedges, hsupp, hrec⟩ :=
    h .G0 (-1) 0 (by norm_num) hsupport
  have h := hrec 0
  change coordinate w 0 = (1 : ℝ) at h
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_tail_interior) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_tail_interior, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀     (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hpath0 : path 0 = e)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))),
    ∃ (b : ℕ → Label) (y : ℕ → ℝ) (q : ℕ → Guard),
      q 0 = s ∧ y 0 = compose w (x 0) ∧
      (∀ p, nextGuard (q p) (b p) = some (q (p + 1))) ∧
      (∀ p, InSupport (q p) (y p)) ∧
      (∀ p, y p = r.readout () () (b p) (y (p + 1))) ∧
      (∀ p (hp : p < w.length), b p = w[p]) ∧
      (∀ p, b (w.length + p) = a p) ∧
      (∀ p, y (w.length + p) = x p)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, y, q, hq0, hy0, hedges, hsupp, hrec, hprefix, hbFuture, hyFuture⟩ :=
    h .G0 .G0 [] rfl (fun _ => Label.L0) (fun _ => 0) (fun _ => .G0) rfl
      (fun _ => rfl) (fun _ => LiteralBranchReadout.zero_supported)
      (by intro p; norm_num [branch, shift])
  have h := hrec 0
  change y 0 = (1 : ℝ) at h
  norm_num [compose] at hy0
  rw [hy0] at h
  norm_num at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.prepend_legal_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.prepend_legal_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

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
  realize.{0,0,0,0,0} observationSignature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V) (z : ℝ),
    z ∈ CompetingT o θ s Q V h W ↔ InSupport s (r.readout () () z) ∧
      BlockSupply o θ false Q h z ∧ ∀ i, BlockSupply o θ false V (W i) z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have supported : InSupport .G0 (0 : ℝ) :=
    ⟨by norm_num, (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le⟩
  have member : (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) := by
    refine ⟨supported, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro i p hp
      simp at hp
  have impossible := ((h (fun _ => false) 0 .G0 [] [] [] (fun _ => [])
    rfl rfl 0).mp member).1.1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingT_mem_actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingT_mem_actual, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

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
  realize.{0,0,0,0,0} observationSignature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (lo hi : ℝ) (w : List Label) (cs : List Color)
    (cert : EndpointCertificate θ lo hi w cs)
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi),
    BlockSupply o (r.readout () () θ) false w cs x

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bounds := cut_bounds (0 : Color)
  norm_num only [Fin.val_zero, zero_add] at bounds
  have supportedLo : InSupport .G0 (cut 0) :=
    ⟨bounds.1, bounds.2.1.le.trans bounds.2.2⟩
  have supportedHi : InSupport .G0 (cut 1) :=
    ⟨bounds.1.trans bounds.2.1.le, bounds.2.2⟩
  have costLo : max (cut 0 - cut 0) (max 0 (cut 0 - cut 1)) ≤ (0 : ℝ) := by
    rw [sub_self, max_eq_left (sub_nonpos.mpr bounds.2.1.le)]
    norm_num
  have costHi : max (cut 0 - cut 1) (max 0 (cut 1 - cut 1)) ≤ (0 : ℝ) := by
    rw [sub_self]
    norm_num only [max_self]
    rw [max_eq_right (sub_nonpos.mpr bounds.2.1.le)]
  have cert : EndpointCertificate 0 (cut 0) (cut 1) [] [(0 : Color)] := by
    intro p hp
    have hp0 : p = 0 := by simpa only [List.length_singleton, Nat.lt_one_iff] using hp
    subst p
    simpa [compose] using And.intro (And.intro supportedLo costLo) (And.intro supportedHi costHi)
  have bad := h (fun _ => false) 0 le_rfl (cut 0) (cut 1) [] [(0 : Color)] cert
    ((cut 0 + cut 1) / 2) (by linarith [bounds.2.1]) (by linarith [bounds.2.1])
  obtain ⟨error, impossible, _⟩ := bad 0 (by simp)
  change |error| ≤ (-1 : ℝ) at impossible
  linarith [abs_nonneg error]

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.certificate_actual_slots) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.certificate_actual_slots, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

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
  realize.{0,0,0,0,0} observationSignature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (θ : ℝ)
    (u v : List Label) (cu cv : List Color) (hlen : u.length = cu.length) (z : ℝ)
    (hu : BlockSupply o θ false u cu (compose v z))
    (hv : BlockSupply o θ false v cv z),
    BlockSupply o (r.readout () () θ) false (u ++ v) (cu ++ cv) z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hu : BlockSupply (fun _ => false) 0 false [] [] (compose [] (-1)) := by
    intro p hp
    simp at hp
  have hv : BlockSupply (fun _ => false) 0 false [] [observe (fun _ => false) (-1) 0] (-1) := by
    intro p hp
    have hp0 : p = 0 := by simpa only [List.length_singleton, Nat.lt_one_iff] using hp
    subst p
    refine ⟨0, by norm_num, ?_⟩
    simp [compose]
  have bad := h (fun _ => false) 0 [] [] [] [observe (fun _ => false) (-1) 0]
    rfl (-1) hu hv
  obtain ⟨error, impossible, _⟩ := bad 0 (by simp)
  change |error| ≤ (-1 : ℝ) at impossible
  linarith [abs_nonneg error]

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.block_supply_append) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.block_supply_append, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172
