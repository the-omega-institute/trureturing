/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamGeometry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamGeometry
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual fixed-past rays, numbered refinements and intrinsic finite beams. -/
import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion (historyWindow)
open scoped BigOperators

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)

/-- A subset with its entire actual past, at an INTEGER cut. -/
def ray (alpha : History G) (n : ℤ) : Set (History G) :=
  {x | ∀ k, k ≤ n → x.val k = alpha.val k}

def endpoint (alpha : History G) (n : ℤ) : V := G.target (alpha.val n)

@[simp] theorem self_mem_ray (alpha : History G) (n : ℤ) : alpha ∈ ray G alpha n :=
  fun _ _ => rfl

theorem ray_eq_of_mem {alpha x : History G} {n : ℤ} (hx : x ∈ ray G alpha n) :
    ray G x n = ray G alpha n := by
  ext y
  constructor
  · intro hy k hk
    exact (hy k hk).trans (hx k hk)
  · intro hy k hk
    exact (hy k hk).trans (hx k hk).symm

theorem ray_disjoint_or_eq (alpha beta : History G) (n : ℤ) :
    Disjoint (ray G alpha n) (ray G beta n) ∨ ray G alpha n = ray G beta n := by
  classical
  by_cases h : ∃ x, x ∈ ray G alpha n ∧ x ∈ ray G beta n
  · obtain ⟨x, hx, hy⟩ := h
    exact Or.inr ((ray_eq_of_mem G hx).symm.trans (ray_eq_of_mem G hy))
  · exact Or.inl (Set.disjoint_left.mpr (fun x hx hy => h ⟨x, hx, hy⟩))

theorem ray_mono (alpha : History G) {n m : ℤ} (h : n ≤ m) :
    ray G alpha m ⊆ ray G alpha n := fun _ hx k hk => hx k (hk.trans h)

/-- Genuine legal past replacement, retaining EVERY edge strictly after n. -/
def splice (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n)
    (x : ray G alpha n) : History G where
  val k := if k ≤ n then beta.val k else x.val.val k
  property k := by
    by_cases hk : k < n
    · have hk0 : k ≤ n := by omega
      have hk1 : k + 1 ≤ n := by omega
      simpa only [if_pos hk0, if_pos hk1] using beta.property k
    · by_cases hkn : k = n
      · subst k
        have hn1 : ¬ n + 1 ≤ n := by omega
        simp only [if_pos le_rfl, if_neg hn1]
        have hx := congrArg G.target (x.property n le_rfl)
        exact ep.symm.trans (hx.symm.trans (x.val.property n))
      · have hk0 : ¬ k ≤ n := by omega
        have hk1 : ¬ k + 1 ≤ n := by omega
        simpa only [if_neg hk0, if_neg hk1] using x.val.property k

@[simp] theorem splice_past (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) (x : ray G alpha n)
    (k : ℤ) (hk : k ≤ n) : (splice G alpha beta n ep x).val k = beta.val k := by
  simp [splice, hk]

@[simp] theorem splice_future (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) (x : ray G alpha n)
    (k : ℤ) (hk : n < k) : (splice G alpha beta n ep x).val k = x.val.val k := by
  simp [splice, show ¬ k ≤ n by omega]

/-- The inverse replaces the past back; no choice of a future occurs here. -/
def spliceEquiv (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) : ray G alpha n ≃ ray G beta n where
  toFun x := ⟨splice G alpha beta n ep x, fun k hk => splice_past G _ _ _ _ _ k hk⟩
  invFun y := ⟨splice G beta alpha n ep.symm y, fun k hk => splice_past G _ _ _ _ _ k hk⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    by_cases hk : k ≤ n
    · simpa [splice, hk] using (x.property k hk).symm
    · simp [splice, hk]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    by_cases hk : k ≤ n
    · simpa [splice, hk] using (y.property k hk).symm
    · simp [splice, hk]

/-- Distinct pasts are removed only by equality of actual ray SETS. -/
abbrev RayAt (n : ℤ) := {U : Set (History G) // ∃ alpha, U = ray G alpha n}

def rayAt (alpha : History G) (n : ℤ) : RayAt G n := ⟨ray G alpha n, alpha, rfl⟩

def RayAt.representative {n : ℤ} (P : RayAt G n) : History G := Classical.choose P.property

theorem RayAt.set_eq {n : ℤ} (P : RayAt G n) :
    P.val = ray G (RayAt.representative G P) n := Classical.choose_spec P.property

def RayAt.endpoint {n : ℤ} (P : RayAt G n) : V :=
  D5.S3.ConceptDynamics.Coding.StandardBeamGeometry.endpoint G
    (RayAt.representative G P) n

theorem RayAt.nonempty {n : ℤ} (P : RayAt G n) : P.val.Nonempty := by
  rw [RayAt.set_eq G P]
  exact ⟨_, self_mem_ray G _ _⟩

theorem RayAt.eq_of_inter {n : ℤ} (P Q : RayAt G n) (x : History G)
    (hx : x ∈ P.val) (hy : x ∈ Q.val) : P = Q := by
  apply Subtype.ext
  change P.val = Q.val
  rw [RayAt.set_eq G P, RayAt.set_eq G Q]
  rw [RayAt.set_eq G P] at hx
  rw [RayAt.set_eq G Q] at hy
  exact (ray_eq_of_mem G hx).symm.trans (ray_eq_of_mem G hy)

theorem RayAt.endpoint_of_mem {n : ℤ} (P : RayAt G n) (x : History G)
    (hx : x ∈ P.val) : RayAt.endpoint G P =
      D5.S3.ConceptDynamics.Coding.StandardBeamGeometry.endpoint G x n := by
  rw [RayAt.set_eq G P] at hx
  exact (congrArg G.target (hx n le_rfl)).symm

section Essential
variable [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G)

/-- Incoming choice plus the original two infinite tails gives a history at
EVERY vertex and integer cut, also when the graph is deterministic. -/
def vertexHistory (u : V) (n : ℤ) : History G := by
  let e := incomingChoice G hG u
  let w : LegalWord G 1 := ⟨fun _ => e, by intro i hi; omega⟩
  let x : History G := ⟨realized G hG w (by omega), realized_legal G hG w (by omega)⟩
  exact ⟨fun k => x.val (k - n), fun k => by
    simpa [sub_add_eq_add_sub] using x.property (k - n)⟩

@[simp] theorem vertexHistory_endpoint (u : V) (n : ℤ) :
    endpoint G (vertexHistory G hG u n) n = u := by
  dsimp [endpoint, vertexHistory]
  simpa [realized] using incomingChoice_target G hG u

abbrev Out (u : V) := {e : E // G.source e = u}

/-- Maximal OUT-degree, bounded below by one. -/
def Delta : ℕ := max 1 (Finset.univ.sup (fun u : V => Fintype.card (Out G u)))

theorem out_card_le_Delta (u : V) : Fintype.card (Out G u) ≤ Delta G :=
  (Finset.le_sup (f := fun u : V => Fintype.card (Out G u)) (Finset.mem_univ u)).trans
    (le_max_right _ _)

/-- All actual edge sequences, with parallel edge numbers intact. -/
def Continuation (u : V) : ℕ → Type v
  | 0 => PUnit
  | r + 1 => Σ e : Out G u, Continuation (G.target e.val) r

instance continuationFintype (u : V) (r : ℕ) : Fintype (Continuation G u r) := by
  induction r generalizing u with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih =>
    letI (v : V) := ih v
    exact inferInstanceAs (Fintype (Σ e : Out G u, Continuation G (G.target e.val) r))

def continuationEnd {u : V} : {r : ℕ} → Continuation G u r → V
  | 0, _ => u
  | _ + 1, p => continuationEnd p.2

/-- Extend one prescribed past by one ACTUAL outgoing edge, then a legal tail. -/
def appendOne (alpha : History G) (n : ℤ) (e : Out G (endpoint G alpha n)) :
    History G where
  val k := if k ≤ n then alpha.val k
    else forwardTail G hG e.val (k - n - 1).toNat
  property k := by
    by_cases hk : k < n
    · have h0 : k ≤ n := by omega
      have h1 : k + 1 ≤ n := by omega
      simpa only [if_pos h0, if_pos h1] using alpha.property k
    · by_cases hkn : k = n
      · subst k
        have h1 : ¬ n + 1 ≤ n := by omega
        simp only [if_pos le_rfl, if_neg h1]
        have hzero : (n + 1 - n - 1).toNat = 0 := by omega
        simpa only [hzero, endpoint, forwardTail, Function.iterate_zero_apply] using e.property.symm
      · have h0 : ¬ k ≤ n := by omega
        have h1 : ¬ k + 1 ≤ n := by omega
        have hd : (k + 1 - n - 1).toNat = (k - n - 1).toNat + 1 := by omega
        simp only [if_neg h0, if_neg h1, hd]
        exact forwardTail_seam G hG _ _

@[simp] theorem appendOne_past (alpha : History G) (n : ℤ)
    (e : Out G (endpoint G alpha n)) (k : ℤ) (hk : k ≤ n) :
    (appendOne G hG alpha n e).val k = alpha.val k := by simp [appendOne, hk]

@[simp] theorem appendOne_edge (alpha : History G) (n : ℤ)
    (e : Out G (endpoint G alpha n)) : (appendOne G hG alpha n e).val (n + 1) = e.val := by
  simp [appendOne, show ¬ n + 1 ≤ n by omega, forwardTail]

@[simp] theorem appendOne_endpoint (alpha : History G) (n : ℤ)
    (e : Out G (endpoint G alpha n)) :
    endpoint G (appendOne G hG alpha n e) (n + 1) = G.target e.val := by
  simp [endpoint]

def continuationEquiv (alpha : History G) (n : ℤ)
    (e : Out G (endpoint G alpha n)) (r : ℕ) :
    Continuation G (endpoint G (appendOne G hG alpha n e) (n + 1)) r ≃
      Continuation G (G.target e.val) r :=
  Equiv.cast (congrArg (fun u : V => Continuation G u r)
    (appendOne_endpoint G hG alpha n e))

theorem continuationEnd_cast {u v : V} (h : u = v) (r : ℕ)
    (p : Continuation G v r) :
    continuationEnd G
        ((Equiv.cast (congrArg (fun w : V => Continuation G w r) h)).symm p) =
      continuationEnd G p := by
  cases h
  rfl

/-- One-step equality of actual subsets, with every arbitrary future present. -/
theorem ray_refine_one (alpha : History G) (n : ℤ) :
    ray G alpha n = ⋃ e : Out G (endpoint G alpha n),
      ray G (appendOne G hG alpha n e) (n + 1) := by
  ext x
  constructor
  · intro hx
    let e : Out G (endpoint G alpha n) := ⟨x.val (n + 1), by
      exact (x.property n).symm.trans (congrArg G.target (hx n le_rfl))⟩
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    intro k hk
    by_cases hkn : k ≤ n
    · simpa only [appendOne_past G hG alpha n e k hkn] using hx k hkn
    · have he : k = n + 1 := by omega
      subst k
      exact (appendOne_edge G hG alpha n e).symm
  · intro hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    intro k hk
    exact (he k (by omega)).trans (appendOne_past G hG alpha n e k hk)

theorem ray_refine_one_disjoint (alpha : History G) (n : ℤ)
    {e f : Out G (endpoint G alpha n)} (hef : e ≠ f) :
    Disjoint (ray G (appendOne G hG alpha n e) (n + 1))
      (ray G (appendOne G hG alpha n f) (n + 1)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hef
  apply Subtype.ext
  exact (appendOne_edge G hG alpha n e).symm.trans
    ((hx (n + 1) le_rfl).symm.trans
      ((hy (n + 1) le_rfl).trans (appendOne_edge G hG alpha n f)))

/-- Recursive numbered-word extension. Every recursion advances the INTEGER cut. -/
def refined (alpha : History G) (n : ℤ) :
    (r : ℕ) → Continuation G (endpoint G alpha n) r → History G
  | 0, _ => alpha
  | r + 1, p =>
    refined (appendOne G hG alpha n p.1) (n + 1) r
      ((continuationEquiv G hG alpha n p.1 r).symm p.2)

@[simp] theorem refined_endpoint (alpha : History G) (n : ℤ) (r : ℕ)
    (p : Continuation G (endpoint G alpha n) r) :
    endpoint G (refined G hG alpha n r p) (n + (r : ℤ)) = continuationEnd G p := by
  induction r generalizing alpha n with
  | zero => simp [refined, continuationEnd]
  | succ r ih =>
    cases p with
    | mk e p =>
      let ce := continuationEquiv G hG alpha n e r
      have hh := ih (appendOne G hG alpha n e) (n + 1) (ce.symm p)
      have hcont : continuationEnd G (ce.symm p) = continuationEnd G p := by
        exact continuationEnd_cast G (appendOne_endpoint G hG alpha n e) r p
      convert hh using 1 <;>
        simp [refined, continuationEnd, ce, Int.natCast_add, Int.natCast_one,
          add_assoc, add_left_comm, add_comm, appendOne_endpoint, hcont]

/-- Exact finite, pairwise disjoint r-step refinement through n+r. -/
theorem ray_refine (alpha : History G) (n : ℤ) (r : ℕ) :
    ray G alpha n = ⋃ p : Continuation G (endpoint G alpha n) r,
      ray G (refined G hG alpha n r p) (n + (r : ℤ)) := by
  induction r generalizing alpha n with
  | zero =>
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨PUnit.unit, by simpa [refined] using hx⟩
    · intro x hx
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
      simpa [refined] using hp
  | succ r ih =>
    rw [ray_refine_one G hG alpha n]
    simp only [Continuation, Set.iUnion_sigma]
    apply Set.iUnion_congr
    intro e
    have hr := ih (appendOne G hG alpha n e) (n + 1)
    let ce := continuationEquiv G hG alpha n e r
    have hri : (⋃ p : Continuation G (endpoint G (appendOne G hG alpha n e) (n + 1)) r,
        ray G (refined G hG (appendOne G hG alpha n e) (n + 1) r p)
          (n + 1 + (r : ℤ))) =
        ⋃ a : Continuation G (G.target e.val) r,
          ray G (refined G hG alpha n (r + 1) ⟨e, a⟩) (n + ((r + 1 : ℕ) : ℤ)) := by
      apply Set.iUnion_congr_of_surjective ce ce.surjective
      intro p
      have hp : ce.symm (ce p) = p := ce.left_inv p
      simpa only [refined, Int.natCast_add, Int.natCast_one, add_assoc, add_left_comm,
        add_comm, appendOne_endpoint] using
        congrArg (fun z => ray G (refined G hG (appendOne G hG alpha n e) (n + 1) r z)
          (n + 1 + (r : ℤ))) hp
    have := hr.trans hri
    simpa only [Int.natCast_add, Int.natCast_one, add_assoc, add_left_comm, add_comm] using this

theorem refined_ray_subset (alpha : History G) (n : ℤ) (r : ℕ)
    (p : Continuation G (endpoint G alpha n) r) :
    ray G (refined G hG alpha n r p) (n + (r : ℤ)) ⊆ ray G alpha n := by
  rw [ray_refine G hG alpha n r]
  exact Set.subset_iUnion (fun q =>
    ray G (refined G hG alpha n r q) (n + (r : ℤ))) p

theorem ray_refine_disjoint (alpha : History G) (n : ℤ) (r : ℕ)
    {p q : Continuation G (endpoint G alpha n) r} (hpq : p ≠ q) :
    Disjoint (ray G (refined G hG alpha n r p) (n + (r : ℤ)))
      (ray G (refined G hG alpha n r q) (n + (r : ℤ))) := by
  induction r generalizing alpha n with
  | zero =>
    cases p with
    | unit =>
      cases q with
      | unit => exact (hpq rfl).elim
  | succ r ih =>
    by_cases he : p.1 = q.1
    · cases p with
      | mk e p =>
        cases q with
        | mk f q =>
          dsimp only at he
          subst f
          have h : p ≠ q := fun h => hpq (by cases h; rfl)
          let ce := continuationEquiv G hG alpha n e r
          have h' : ce.symm p ≠ ce.symm q := by
            intro h'
            exact h (ce.symm.injective h')
          have hh := ih (appendOne G hG alpha n e) (n + 1) h'
          convert hh using 1 <;>
            simp [refined, ce, appendOne_endpoint, Int.natCast_add, Int.natCast_one,
              add_assoc, add_left_comm, add_comm]
    · have hd := ray_refine_one_disjoint G hG alpha n he
      cases p with
      | mk e p =>
        cases q with
        | mk f q =>
          have heq : Continuation G (endpoint G (appendOne G hG alpha n e) (n + 1)) r =
              Continuation G (G.target e.val) r := by rw [appendOne_endpoint]
          let ce : Continuation G (endpoint G (appendOne G hG alpha n e) (n + 1)) r ≃
              Continuation G (G.target e.val) r := Equiv.cast heq
          let cf := continuationEquiv G hG alpha n f r
          let pe := (continuationEquiv G hG alpha n e r).symm p
          let qf := (continuationEquiv G hG alpha n f r).symm q
          exact hd.mono
            (by simpa [refined, pe, appendOne_endpoint, Int.natCast_add, Int.natCast_one,
              add_assoc, add_left_comm, add_comm] using
              refined_ray_subset G hG (appendOne G hG alpha n e) (n + 1) r pe)
            (by simpa [refined, qf, appendOne_endpoint, Int.natCast_add, Int.natCast_one,
              add_assoc, add_left_comm, add_comm] using
              refined_ray_subset G hG (appendOne G hG alpha n f) (n + 1) r qf)

theorem continuation_card_bound (u : V) (r : ℕ) :
    Fintype.card (Continuation G u r) ≤ Delta G ^ r := by
  induction r generalizing u with
  | zero =>
    change Fintype.card PUnit ≤ 1
    rw [Fintype.card_punit]
  | succ r ih =>
    change Fintype.card (Σ e : Out G u, Continuation G (G.target e.val) r) ≤ _
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _e : Out G u, Delta G ^ r := Finset.sum_le_sum (fun e _ => ih _)
      _ = Fintype.card (Out G u) * Delta G ^ r := by simp
      _ ≤ Delta G * Delta G ^ r := Nat.mul_le_mul_right _ (out_card_le_Delta G u)
      _ = Delta G ^ (r + 1) := (pow_succ' _ _).symm

/-- Intrinsic partition: the actual ray subsets, not an endpoint set. -/
def Parts (U : Set (History G)) (n : ℤ) := {P : RayAt G n // P.val ⊆ U}

/-- Exact finite partition of a set. Finiteness and saturation are independent:
a finite collection of selected points would not prove this property. -/
def AtCut (U : Set (History G)) (n : ℤ) : Prop :=
  Finite (Parts G U n) ∧ ∀ x ∈ U, ray G x n ⊆ U

def IsBeam (U : Set (History G)) : Prop := ∃ n : ℤ, AtCut G U n
abbrev Beam := {U : Set (History G) // IsBeam G U}

/-- Refinements are precisely the intrinsic ray pieces of the original ray. -/
def rayPartsEquiv (alpha : History G) (n : ℤ) (r : ℕ) :
    Continuation G (endpoint G alpha n) r ≃ Parts G (ray G alpha n) (n + (r : ℤ)) := by
  let f : Continuation G (endpoint G alpha n) r →
      Parts G (ray G alpha n) (n + (r : ℤ)) := fun p =>
    ⟨rayAt G (refined G hG alpha n r p) _, refined_ray_subset G hG alpha n r p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q heq
    by_contra hpq
    have hd := ray_refine_disjoint G hG alpha n r hpq
    have hs := congrArg (fun P => P.val.val) heq
    have hs' : ray G (refined G hG alpha n r p) (n + (r : ℤ)) =
        ray G (refined G hG alpha n r q) (n + (r : ℤ)) := hs
    have hx : refined G hG alpha n r p ∈
        ray G (refined G hG alpha n r q) (n + (r : ℤ)) := by
      have hx' := self_mem_ray G (refined G hG alpha n r p) (n + (r : ℤ))
      rw [hs'] at hx'
      exact hx'
    exact Set.disjoint_left.mp hd (self_mem_ray G _ _) hx
  · intro P
    obtain ⟨x, hx⟩ := RayAt.nonempty G P.val
    have hu := P.property hx
    rw [ray_refine G hG alpha n r] at hu
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hu
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact RayAt.eq_of_inter G _ _ x hp hx

theorem ray_atCut (hG : Essential G) (alpha : History G) (n : ℤ) :
    AtCut G (ray G alpha n) n := by
  haveI : Finite (Parts G (ray G alpha n) n) :=
    Finite.of_equiv (Continuation G (endpoint G alpha n) 0)
      (by simpa using rayPartsEquiv G hG alpha n 0)
  refine ⟨inferInstance, ?_⟩
  intro x hx
  rw [ray_eq_of_mem G hx]

theorem ray_atCut_later (hG : Essential G) (alpha : History G) {n m : ℤ} (hnm : n ≤ m) :
    AtCut G (ray G alpha n) m := by
  let r := (m - n).toNat
  have hm : n + (r : ℤ) = m := by dsimp [r]; omega
  haveI : Finite (Parts G (ray G alpha n) m) :=
    Finite.of_equiv (Continuation G (endpoint G alpha n) r)
      (hm ▸ rayPartsEquiv G hG alpha n r)
  refine ⟨inferInstance, ?_⟩
  intro x hx y hy k hk
  exact (hy k (hk.trans hnm)).trans (hx k hk)

theorem parts_union {U : Set (History G)} {n : ℤ} (hU : AtCut G U n) :
    U = ⋃ P : Parts G U n, P.val.val := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨⟨rayAt G x n, hU.2 x hx⟩, self_mem_ray G x n⟩
  · intro hx
    obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
    exact P.property hx

theorem parts_disjoint {U : Set (History G)} {n : ℤ} (P Q : Parts G U n) (hpq : P ≠ Q) :
    Disjoint P.val.val Q.val.val := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hpq (Subtype.ext (RayAt.eq_of_inter G P.val Q.val x hx hy))

/-- Each finer intrinsic piece belongs to exactly one earlier intrinsic piece. -/
def partsRefinementEquiv {U : Set (History G)} {n m : ℤ}
    (hU : AtCut G U n) (hnm : n ≤ m) :
    (Σ P : Parts G U n, Parts G P.val.val m) ≃ Parts G U m where
  toFun P := ⟨P.2.val, P.2.property.trans P.1.property⟩
  invFun Q := by
    let x := RayAt.representative G Q.val
    have hx : x ∈ Q.val.val := by rw [RayAt.set_eq G Q.val]; exact self_mem_ray G _ _
    let P : Parts G U n := ⟨rayAt G x n, hU.2 x (Q.property hx)⟩
    exact ⟨P, Q.val, by
      rw [RayAt.set_eq G Q.val]
      exact ray_mono G x hnm⟩
  left_inv P := by
    have hx : RayAt.representative G P.2.val ∈ P.2.val.val := by
      rw [RayAt.set_eq G P.2.val]; exact self_mem_ray G _ _
    have hP : rayAt G (RayAt.representative G P.2.val) n = P.1.val :=
      RayAt.eq_of_inter G _ _ _ (self_mem_ray G _ _) (P.2.property hx)
    apply Sigma.ext
    · exact Subtype.ext hP
    · apply (Subtype.heq_iff_coe_eq (fun Q => by
        rw [congrArg Subtype.val hP])).mpr
      rfl
  right_inv Q := by apply Subtype.ext; rfl

/-- Common-cut compatibility is refinement of actual pieces, including
cross-cut equality caused by unique continuation. No endpoint quotient is used. -/
theorem atCut_mono (hG : Essential G) {U : Set (History G)} {n m : ℤ}
    (hU : AtCut G U n) (hnm : n ≤ m) :
    AtCut G U m := by
  letI : Finite (Parts G U n) := hU.1
  letI (P : Parts G U n) : Finite (Parts G P.val.val m) := by
    rw [RayAt.set_eq G P.val]
    exact (ray_atCut_later G hG _ hnm).1
  haveI : Finite (Parts G U m) := Finite.of_equiv _ (partsRefinementEquiv G hU hnm)
  refine ⟨inferInstance, ?_⟩
  intro x hx
  exact (ray_mono G x hnm).trans (hU.2 x hx)

/-- If the SAME ray set occurs at n and m≥n, its entire numbered refinement
has one piece. This is an actual unique-continuation assertion across cuts. -/
theorem equal_ray_unique_continuation (hG : Essential G) (alpha beta : History G) {n m : ℤ}
    (hnm : n ≤ m) (heq : ray G alpha n = ray G beta m) :
    Fintype.card (Continuation G (endpoint G alpha n) (m - n).toNat) = 1 := by
  let r := (m - n).toNat
  have hm : n + (r : ℤ) = m := by dsimp [r]; omega
  have e := rayPartsEquiv G hG alpha n r
  have e0 := rayPartsEquiv G hG beta m 0
  have e0' : Continuation G (endpoint G beta m) 0 ≃ Parts G (ray G beta m) m := by
    convert e0 using 1 <;> simp
  have hParts : Parts G (ray G alpha n) (n + (r : ℤ)) =
      Parts G (ray G beta m) m := by
    rw [hm, heq]
  have e' : Continuation G (endpoint G alpha n) r ≃
      Continuation G (endpoint G beta m) 0 :=
    e.trans ((Equiv.cast hParts).trans e0'.symm)
  have hc := Fintype.card_congr e'
  have hc0 : Fintype.card (Continuation G (endpoint G beta m) 0) = 1 := by
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  rw [hc0] at hc
  simpa [r] using hc

/-- Finite unions normalize INTRINSICALLY: coincident pasts disappear;
coincident endpoints in distinct rays do not disappear. -/
theorem atCut_iUnion {I : Type*} [Finite I] (U : I → Set (History G)) (n : ℤ)
    (hU : ∀ i, AtCut G (U i) n) : AtCut G (⋃ i, U i) n := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI (i : I) : Finite (Parts G (U i) n) := (hU i).1
  let f : (Σ i, Parts G (U i) n) → Parts G (⋃ i, U i) n := fun P =>
    ⟨P.2.val, P.2.property.trans (Set.subset_iUnion _ P.1)⟩
  have hf : Function.Surjective f := by
    intro P
    obtain ⟨x, hx⟩ := RayAt.nonempty G P.val
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.property hx)
    have hs : P.val.val ⊆ U i := by
      have he : P.val = rayAt G x n :=
        RayAt.eq_of_inter G _ _ x hx (self_mem_ray G x n)
      rw [he]
      exact (hU i).2 x hi
    exact ⟨⟨i, P.val, hs⟩, Subtype.ext rfl⟩
  haveI : Finite (Parts G (⋃ i, U i) n) := Finite.of_surjective f hf
  refine ⟨inferInstance, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ((hU i).2 x hi).trans (Set.subset_iUnion _ i)

end Essential
end D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
