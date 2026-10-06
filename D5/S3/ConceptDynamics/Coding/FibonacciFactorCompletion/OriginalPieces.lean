/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OriginalPieces
   generality: G
   anchors: []
   utility: none
   digest: A selected competing scalar lifts one fixed tail through every original full-containing piece path. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

/-- Endpoint singletons and whole consecutive-endpoint intervals, with their actual guard. -/
structure OriginalPiece (B : Finset ℝ) (s : Guard) where
  lo : ℝ
  hi : ℝ
  lo_mem : lo ∈ B
  hi_mem : hi ∈ B
  ordered : lo ≤ hi
  lo_support : InSupport s lo
  hi_support : InSupport s hi
  consecutive : ∀ z ∈ B, ¬ (lo < z ∧ z < hi)

def piece_carrier {B : Finset ℝ} {s : Guard} (P : OriginalPiece B s) : Set ℝ :=
  Set.Icc P.lo P.hi

/-- Full original edges retain both the legal root domain and entire target containment. -/
structure OriginalPiecePath (B : Finset ℝ) (A : List Label) (s : Guard)
    (terminal : OriginalPiece B s) where
  guards : ℕ → Guard
  pieces : (p : ℕ) → OriginalPiece B (guards p)
  initial_guard : guards 0 = .G0
  terminal_guard : guards A.length = s
  terminal_piece : (piece_carrier (pieces A.length)) = (piece_carrier terminal)
  edges : ∀ p (hp : p < A.length),
    nextGuard (guards p) A[p] = some (guards (p+1)) ∧
    (∀ z ∈ (piece_carrier (pieces p)), ∃ y, InSupport (guards (p+1)) y ∧ z = branch A[p] y) ∧
    (∀ y ∈ (piece_carrier (pieces (p+1))), branch A[p] y ∈ (piece_carrier (pieces p)))

/-- One terminal scalar propagates jointly through every full-containing edge. -/
theorem original_piece_suffix_membership (A : List Label) (pieces : ℕ → Set ℝ) (z : ℝ)
    (terminal : z ∈ pieces A.length)
    (edges : ∀ p (hp : p < A.length), ∀ y ∈ pieces (p+1), branch A[p] y ∈ pieces p) :
    ∀ p, p ≤ A.length → compose (A.drop p) z ∈ pieces p := by
  induction A generalizing pieces with
  | nil =>
    intro p hp
    have zero : p = 0 := by simpa using hp
    subst p
    exact terminal
  | cons l A ih =>
    have remaining := ih (fun p => pieces (p+1)) terminal (by
      intro p hp y hy
      exact edges (p+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hp) y hy)
    intro p hp
    cases p with
    | zero =>
      exact edges 0 (by simp) _ (remaining 0 (Nat.zero_le _))
    | succ p =>
      simpa only [List.drop_succ_cons,Nat.succ_eq_add_one] using
        remaining p (by simp only [List.length_cons] at hp; omega)

/-- Selection in K intersect P2 fixes one actual scalar, literal tail and guard future.
Every finite history uses those same data and lifts into its specified original pieces. -/
theorem selected_original_piece_tail
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length)
    (B : Finset ℝ) (P2 : OriginalPiece B s)
    (selection : ({z : ℝ | ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W} ∩ (piece_carrier P2)).Nonempty)
    (paths : ∀ zs : List Bool, OriginalPiecePath B (Q++choiceBlocks (fun _ => V) zs) s P2) :
    ∃ (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧ x 0 ∈ (piece_carrier P2) ∧
      (∀ p, nextGuard (path p) (tail p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (tail p) (x (p+1))) ∧
      (∀ n, (compose V)^[n] (x 0) ∈ CompetingT o θ s Q V h W) ∧
      ∀ zs : List Bool, ∃ (beta : ℕ → Label) (X : ℕ → ℝ) (q : ℕ → Guard),
        q 0 = .G0 ∧
        (∀ p, nextGuard (q p) (beta p) = some (q (p+1))) ∧
        (∀ p, InSupport (q p) (X p)) ∧
        (∀ p, X p = branch (beta p) (X (p+1))) ∧
        (∀ p (hp : p < (Q++choiceBlocks (fun _ => V) zs).length),
          beta p = (Q++choiceBlocks (fun _ => V) zs)[p]) ∧
        (∀ p, beta ((Q++choiceBlocks (fun _ => V) zs).length+p) = tail p ∧
          X ((Q++choiceBlocks (fun _ => V) zs).length+p) = x p ∧
          q ((Q++choiceBlocks (fun _ => V) zs).length+p) = path p) ∧
        (∀ p, p ≤ (Q++choiceBlocks (fun _ => V) zs).length →
          X p ∈ (piece_carrier ((paths zs).pieces p)) ∧ q p = (paths zs).guards p) ∧
        OperationRecord o θ .closed beta (recordWithOmegaTail o (h++choiceBlocks W zs) x) := by
  classical
  obtain ⟨z,orbit,carrier⟩ := selection
  change ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W at orbit
  have supported : InSupport s z := by
    have atZero := orbit 0
    simpa only [Function.iterate_zero, id_eq] using atZero.1
  obtain ⟨tail,x,path,pathZero,scalarZero,tailEdges,tailSupport,tailRec⟩ := lawful_tail s z supported
  refine ⟨tail,x,path,pathZero,by simpa only [scalarZero] using carrier,
    tailEdges,tailSupport,tailRec,by simpa only [scalarZero] using orbit,?_⟩
  intro zs
  let A := Q++choiceBlocks (fun _ => V) zs
  let cs := h++choiceBlocks W zs
  have allSupply := ((competingT_orbit_iff_all_histories o θ s Q V h W hQ hV hQlen hlen z).mp orbit).2
  have supply : BlockSupply o θ false A cs (x 0) := by simpa only [scalarZero] using allSupply zs
  have legal : LegalWord .G0 s A := legal_append .G0 s s Q _ hQ
    (choices_legal s (fun _ => V) (fun _ => hV) zs)
  have lengths : A.length = cs.length := by
    simp only [A,cs,List.length_append,hQlen,choice_lengths (fun _ => V) W hlen zs]
  obtain ⟨beta,X,omega,pre,future,coordinates,record⟩ := actual_omega_prefix_record
    o θ hθ s A cs lengths legal tail x path pathZero tailEdges tailSupport tailRec supply
  obtain ⟨q,qZero,qEdges,qSupport,qRec⟩ := omega
  have qPrefix : ∀ p, p ≤ A.length → q p = (paths zs).guards p := by
    intro p
    induction p with
    | zero => intro _; exact qZero.trans (paths zs).initial_guard.symm
    | succ p ih =>
      intro hp
      have before := ih (by omega)
      have edge := ((paths zs).edges p (by change p < A.length; omega)).1
      have actual := qEdges p
      rw [before,pre p (by omega)] at actual
      exact Option.some.inj (actual.symm.trans edge)
  have qEnd : q A.length = s := (qPrefix _ le_rfl).trans (paths zs).terminal_guard
  have qFuture (p : ℕ) : q (A.length+p) = path p := by
    induction p with
    | zero => simpa only [Nat.add_zero,pathZero] using qEnd
    | succ p ih =>
      have actual := qEdges (A.length+p)
      rw [ih,future p] at actual
      have expected := tailEdges p
      exact Option.some.inj (by simpa only [Nat.add_assoc,Nat.succ_eq_add_one] using actual.symm.trans expected)
  have XEnd : X A.length = z := by simpa only [Nat.add_zero,scalarZero] using coordinates 0
  have prefixScalars := prefix_coordinates A beta X z pre qRec XEnd
  have wholePath := original_piece_suffix_membership A (fun p => (piece_carrier ((paths zs).pieces p))) z
    (by rw [(paths zs).terminal_piece]; exact carrier)
    (fun p hp => ((paths zs).edges p hp).2.2)
  refine ⟨beta,X,q,qZero,qEdges,qSupport,qRec,pre,?_,?_,record⟩
  · intro p
    exact ⟨future p,coordinates p,qFuture p⟩
  · intro p hp
    exact ⟨by rw [prefixScalars p hp]; exact wholePath p hp,qPrefix p hp⟩

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
