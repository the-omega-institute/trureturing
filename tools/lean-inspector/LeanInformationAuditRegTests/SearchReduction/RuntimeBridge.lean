import LeanInformationAuditRegTests.SearchReduction.CertificateModel

/-! Bridges for the production arm projection, DP and certificate boundary.
The completion hypotheses describe graph relations, including actual support;
they do not assert correctness of the unsafe metaprogram or its disk index. -/

namespace LeanInformationAudit.Tests.SearchReduction.RuntimeBridge
open LeanInformationAudit.SearchReduction
open GraphModel CertificateModel

/-- A positive replay preserves its proof and support at the actual boundary. -/
theorem replay_boundary (certificate : ObviousCertificate) (result : LocalResult)
    (accepted : (certificateOnlyResult certificate result).cost = .zero) :
    result.cost = .zero ∧ result.proof?.isSome = true ∧
    (certificateOnlyResult certificate result).proof? = result.proof? ∧
    (certificateOnlyResult certificate result).used = result.used ∧
    (certificateOnlyResult certificate result).certificate? = some certificate := by
  unfold certificateOnlyResult at *
  split at accepted
  · rename_i valid
    simp only [Bool.and_eq_true, beq_iff_eq] at valid
    simp [valid.1, valid.2]
  · contradiction

/-- The actual arm graph consumes precisely the checked lambda's support,
including its order, rather than all visible or author premises. -/
theorem attached_certificate_arm_support (edge : GraphEdge)
    (certificate : ObviousCertificate) (proof : Lean.Expr) (used : List Nat)
    (paired : Bool) :
    let attached := attachCertificate edge paired certificate proof used
    let graph : ProofGraph := {edges := [attached]}
    ((armGraph graph paired false).edges.map fun e =>
      (e.conclusion, e.premises, e.cost,
        if paired then e.pairedZeroProof else e.zeroProof)) =
      [(edge.conclusion, used, .zero, some proof)] := by
  cases paired <;>
    simp [armGraph, attachCertificate, edgeActive]

/-- Unknown lower projections optimistically allow every premise to vanish.
This is a support change, not merely a zero numerical edge weight. -/
theorem unknown_author_lower_support (edge : GraphEdge)
    (author : edge.window = 1) (unknown : edge.cost = .unknown) :
    ((armGraph {edges := [edge]} false false true).edges.map (·.premises)) = [[]] := by
  simp [armGraph, edgeActive, author, unknown]

/-- An unresolved non-author shortcut is absent even from the lower graph. -/
theorem unknown_shortcut_absent (edge : GraphEdge)
    (shortcut : edge.window ≠ 1) (unknown : edge.cost = .unknown) :
    (armGraph {edges := [edge]} false false true).edges = [] := by
  simp [armGraph, edgeActive, shortcut, unknown]

/-- Graph simulation permits a checked certificate to discard premises. -/
def Simulates (cheap expensive : ProofGraph)
    (cheapWeight expensiveWeight : EdgeCost → Nat) : Prop :=
  ∀ e ∈ expensive.edges, ∃ r ∈ cheap.edges,
    r.conclusion = e.conclusion ∧
    (∀ p ∈ r.premises, p ∈ e.premises) ∧
    cheapWeight r.cost ≤ expensiveWeight e.cost

private theorem budget_mono (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (fuel v a b : Nat) (ab : a ≤ b)
    (h : Derivable graph price seeds fuel v a) :
    Derivable graph price seeds fuel v b := by
  induction fuel generalizing v a b with
  | zero => exact h
  | succ fuel ih =>
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact Or.inl hs
    · exact Or.inr ⟨edge, he, le_trans hc ab,
        fun p hm => ih p _ _ (Nat.sub_le_sub_right ab _) (hp p hm)⟩

theorem support_simulation (cheap expensive : ProofGraph)
    (cw ew : EdgeCost → Nat) (seeds : List Nat)
    (simulation : Simulates cheap expensive cw ew) (fuel v n : Nat)
    (h : Derivable expensive (fun e => ew e.cost) seeds fuel v n) :
    Derivable cheap (fun e => cw e.cost) seeds fuel v n := by
  induction fuel generalizing v n with
  | zero => exact h
  | succ fuel ih =>
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact Or.inl hs
    · have em := (List.mem_filter.mp he).1
      have ec : edge.conclusion = v := by simpa using (List.mem_filter.mp he).2
      obtain ⟨r, rm, rc, rp, price⟩ := simulation edge em
      refine Or.inr ⟨r, List.mem_filter.mpr ⟨rm, by simp [rc, ec]⟩,
        le_trans price hc, ?_⟩
      intro p pm
      exact budget_mono cheap _ seeds fuel p _ _
        (Nat.sub_le_sub_left price n) (ih p _ (hp p (rp p pm)))

/-- Index and support obligations required by the real array DP. -/
structure Indexed (graph : ProofGraph) : Prop where
  ids : ∀ i (h : i < graph.vertices.length), (graph.vertices[i]).id = i
  premises : ∀ e ∈ graph.edges, ∀ p ∈ e.premises, p < graph.vertices.length

theorem production_depth_simulation (cheap expensive : ProofGraph)
    (cw ew : EdgeCost → Nat) (seeds : List Nat)
    (ci : Indexed cheap) (ei : Indexed expensive)
    (sameSize : cheap.vertices.length = expensive.vertices.length)
    (simulation : Simulates cheap expensive cw ew)
    (v n : Nat) (valid : v < expensive.vertices.length)
    (bounded : depth expensive ew seeds v ≤ .finite n) :
    depth cheap cw seeds v ≤ .finite n := by
  have vc : v < cheap.vertices.length := by omega
  unfold depth at *
  rw [dpTable_eq_depthFuel expensive ew seeds ei.ids ei.premises v valid] at bounded
  rw [dpTable_eq_depthFuel cheap cw seeds ci.ids ci.premises v vc, sameSize]
  exact (depthFuel_le_iff_derivable ..).mpr
    (support_simulation cheap expensive cw ew seeds simulation _ v n
      ((depthFuel_le_iff_derivable ..).mp bounded))

/-- Every later completed graph must simulate the current upper graph, and
be simulated by the current lower graph. This includes active shortcuts and
the actual support of each successful replay. -/
structure ArmCompletion (graph completed : ProofGraph) (paired : Bool) : Prop where
  lowerIndexed : Indexed (armGraph graph paired false true)
  upperIndexed : Indexed (armGraph graph paired false)
  completedIndexed : Indexed completed
  sameSize : completed.vertices.length = graph.vertices.length
  lowerSimulation : Simulates (armGraph graph paired false true) completed costLower costUpper
  upperSimulation : Simulates completed (armGraph graph paired false) costUpper costUpper

/-- The envelope is for the production armInterval and optimized array DP,
not an independently supplied numerical interval. -/
theorem runtime_dp_completion_envelope (graph completed : ProofGraph) (paired : Bool)
    (completion : ArmCompletion graph completed paired) (v value : Nat)
    (valid : v < graph.vertices.length)
    (exactValue : depth completed costUpper (armSeeds graph paired) v = .finite value) :
    (armInterval graph paired false (some v)).lower ≤ .finite value ∧
    .finite value ≤ (armInterval graph paired false (some v)).upper := by
  have sizeL : (armGraph graph paired false true).vertices.length =
      completed.vertices.length := by simpa [armGraph] using completion.sameSize.symm
  have sizeU : completed.vertices.length =
      (armGraph graph paired false).vertices.length := by simpa [armGraph] using completion.sameSize
  constructor
  · exact production_depth_simulation _ _ _ _ _ completion.lowerIndexed
      completion.completedIndexed sizeL completion.lowerSimulation v value
      (by rw [completion.sameSize]; exact valid)
      (by rw [exactValue]; exact Nat.le_refl _)
  · change .finite value ≤ depth (armGraph graph paired false) costUpper (armSeeds graph paired) v
    cases upper : depth (armGraph graph paired false) costUpper (armSeeds graph paired) v with
    | top => trivial
    | finite n =>
      have b := production_depth_simulation _ _ _ _ _ completion.completedIndexed
        completion.upperIndexed sizeU completion.upperSimulation v n
        (by simpa [armGraph] using valid)
        (by rw [upper]; exact Nat.le_refl _)
      rw [exactValue] at b
      exact b

/-- A positive production classifier entails a strict drop for all completed
graphs satisfying the explicit replay/support/shortcut simulation contract. -/
theorem runtime_positive_completion_drop (reading : GraphReading)
    (baseCompleted pairCompleted : ProofGraph) (baseValue pairValue : Nat)
    (baseCompletion : ArmCompletion reading.graph baseCompleted false)
    (pairCompletion : ArmCompletion reading.graph pairCompleted true)
    (valid : reading.graph.root < reading.graph.vertices.length)
    (baseRead : reading.baseline = armInterval reading.graph false)
    (pairRead : reading.paired = armInterval reading.graph true)
    (baseExact : depth baseCompleted costUpper (armSeeds reading.graph false)
      reading.graph.root = .finite baseValue)
    (pairExact : depth pairCompleted costUpper (armSeeds reading.graph true)
      reading.graph.root = .finite pairValue)
    (positive : classifyGraph reading = .nonBindOnly) : pairValue < baseValue := by
  have bb := runtime_dp_completion_envelope _ _ false baseCompletion _ _ valid baseExact
  have pb := runtime_dp_completion_envelope _ _ true pairCompletion _ _ valid pairExact
  apply interval_strictDrop_sound reading.baseline reading.paired baseValue pairValue
  · simpa [baseRead, armInterval] using bb.1
  · simpa [pairRead, armInterval] using pb.2
  · exact nonBindOnly_requires_strictDrop reading positive

#print axioms replay_boundary
#print axioms attached_certificate_arm_support
#print axioms unknown_author_lower_support
#print axioms unknown_shortcut_absent
#print axioms support_simulation
#print axioms production_depth_simulation
#print axioms runtime_dp_completion_envelope
#print axioms runtime_positive_completion_drop
end LeanInformationAudit.Tests.SearchReduction.RuntimeBridge
