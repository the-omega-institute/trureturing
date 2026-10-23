/- GID: D5/S3/ConceptDynamics/Coding/SameCutWholeRayBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/SameCutWholeRayBridge
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite square forgetting constructs inverse history maps and same-cut images of entire rays. -/
import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization

universe u v w z
variable {V : Type u} {E : Type v} {D : Type w} {R : Type z}
variable (A : DirectedMultigraph V E) (B : DirectedMultigraph V D)

/-- Local square data. `R` is an actual edge type, not an endpoint quotient.
The two operations are phi and phi inverse, totalized off composable inputs.
All global statements are proved below. -/
structure Squares where
  source : R → V
  target : R → V
  sq : R → E → D → R → Prop
  endpoints : ∀ {r x y s}, sq r x y s →
    source r = A.source x ∧ target r = B.source y ∧
    source s = A.target x ∧ target s = B.target y
  back : E → R → R × D
  back_spec : ∀ x s, A.target x = source s →
    sq (back x s).1 x (back x s).2 s
  forth : R → D → E × R
  forth_spec : ∀ r y, target r = B.source y →
    sq r (forth r y).1 y (forth r y).2
  back_unique : ∀ {r r' s x y y'}, sq r x y s → sq r' x y' s →
    r = r' ∧ y = y'
  forth_unique : ∀ {r s s' x x' y}, sq r x y s → sq r x' y s' →
    x = x' ∧ s = s'
  outgoing : ∀ v, {r : R // source r = v}
  incoming : ∀ v, {r : R // target r = v}

variable {A B}

/-- Finite forgetting on actual q-square strips. The left inputs, respectively
right inputs, agree at every position. Other boundaries and the opposite row
are unrestricted. Neither global lift uniqueness nor a ray claim is assumed. -/
structure FiniteForgetting (S : Squares A B (R := R)) (q : ℕ) : Prop where
  positive : 0 < q
  left : ∀ (x : ℕ → E) (y y' : ℕ → D) (r r' : ℕ → R),
    (∀ i, i < q → S.sq (r i) (x i) (y i) (r (i + 1))) →
    (∀ i, i < q → S.sq (r' i) (x i) (y' i) (r' (i + 1))) → r 0 = r' 0
  right : ∀ (x x' : ℕ → E) (y : ℕ → D) (r r' : ℕ → R),
    (∀ i, i < q → S.sq (r i) (x i) (y i) (r (i + 1))) →
    (∀ i, i < q → S.sq (r' i) (x' i) (y i) (r' (i + 1))) → r q = r' q

namespace Squares
variable (S : Squares A B (R := R))

/-- Boundary k is immediately AFTER edge k. -/
structure FullSquare where
  left : History A
  right : History B
  boundary : ℤ → R
  square : ∀ k, S.sq (boundary (k - 1)) (left.val k) (right.val k) (boundary k)

/-- Actual backward recursion through all prescribed past edges. -/
def backRun (x : History A) (n : ℤ) (r : R) : ℕ → R :=
  Nat.rec r (fun d previous => (S.back (x.val (n - (d : ℤ))) previous).1)

def backEdge (x : History A) (n : ℤ) (r : R) (d : ℕ) : D :=
  (S.back (x.val (n - (d : ℤ))) (S.backRun x n r d)).2

theorem backRun_source (x : History A) (n : ℤ) (r : R)
    (hr : S.source r = A.target (x.val n)) (d : ℕ) :
    S.source (S.backRun x n r d) = A.target (x.val (n - (d : ℤ))) := by
  induction d with
  | zero => simpa [backRun] using hr
  | succ d ih =>
    have hs := S.back_spec (x.val (n - (d : ℤ))) (S.backRun x n r d) ih.symm
    have he := (S.endpoints hs).1
    have ht := x.property (n - (d : ℤ) - 1)
    have hk : n - (d : ℤ) - 1 + 1 = n - (d : ℤ) := by omega
    rw [hk] at ht
    have hk' : n - ((d + 1 : ℕ) : ℤ) = n - (d : ℤ) - 1 := by omega
    simpa only [backRun, hk'] using he.trans ht.symm

theorem backRun_square (x : History A) (n : ℤ) (r : R)
    (hr : S.source r = A.target (x.val n)) (d : ℕ) :
    S.sq (S.backRun x n r (d + 1)) (x.val (n - (d : ℤ)))
      (S.backEdge x n r d) (S.backRun x n r d) := by
  exact S.back_spec _ _ (S.backRun_source x n r hr d).symm

/-- Read a finite backward run in increasing time order, retaining every square. -/
theorem backRun_strip (x : History A) (n : ℤ) (r : R)
    (hr : S.source r = A.target (x.val n)) (d i : ℕ) (hi : i < d) :
    S.sq (S.backRun x n r (d - i))
      (x.val (n - (d : ℤ) + (i : ℤ) + 1))
      (S.backEdge x n r (d - (i + 1)))
      (S.backRun x n r (d - (i + 1))) := by
  have hs := S.backRun_square x n r hr (d - (i + 1))
  have hj : d - (i + 1) + 1 = d - i := by omega
  have hk : n - ((d - (i + 1) : ℕ) : ℤ) =
      n - (d : ℤ) + (i : ℤ) + 1 := by omega
  simpa only [hj, hk] using hs

/-- Actual forward phi-inverse recursion; y is an arbitrary full legal history. -/
def forthRun (y : History B) (n : ℤ) (r : R) : ℕ → R :=
  Nat.rec r (fun d previous => (S.forth previous (y.val (n + (d : ℤ) + 1))).2)

def forthEdge (y : History B) (n : ℤ) (r : R) (d : ℕ) : E :=
  (S.forth (S.forthRun y n r d) (y.val (n + (d : ℤ) + 1))).1

theorem forthRun_target (y : History B) (n : ℤ) (r : R)
    (hr : S.target r = B.target (y.val n)) (d : ℕ) :
    S.target (S.forthRun y n r d) = B.target (y.val (n + (d : ℤ))) := by
  induction d with
  | zero => simpa [forthRun] using hr
  | succ d ih =>
    have hs := S.forth_spec (S.forthRun y n r d) (y.val (n + (d : ℤ) + 1))
      (ih.trans (y.property (n + (d : ℤ))))
    simpa [forthRun, Int.natCast_add, add_assoc] using (S.endpoints hs).2.2.2

theorem forthRun_square (y : History B) (n : ℤ) (r : R)
    (hr : S.target r = B.target (y.val n)) (d : ℕ) :
    S.sq (S.forthRun y n r d) (S.forthEdge y n r d)
      (y.val (n + (d : ℤ) + 1)) (S.forthRun y n r (d + 1)) := by
  exact S.forth_spec _ _ ((S.forthRun_target y n r hr d).trans
    (y.property (n + (d : ℤ))))

variable {q : ℕ} (K : FiniteForgetting S q)

/-- The boundary is obtained by q backward squares in the actual future. -/
def leftBoundary (x : History A) (k : ℤ) : R :=
  S.backRun x (k + (q : ℤ)) (S.outgoing (A.target (x.val (k + (q : ℤ))))).val q

theorem leftBoundary_source (x : History A) (k : ℤ) :
    S.source (S.leftBoundary (q := q) x k) = A.target (x.val k) := by
  have h := S.backRun_source x (k + (q : ℤ))
    (S.outgoing (A.target (x.val (k + (q : ℤ))))).val
    (S.outgoing _).property q
  simpa [leftBoundary] using h

include K in
/-- Overlap q squares of a q-run and a (q+1)-run. Left forgetting gives
compatibility of the independently constructed boundaries. -/
theorem leftBoundary_step (x : History A) (k : ℤ) :
    S.leftBoundary (q := q) x (k - 1) =
      (S.back (x.val k) (S.leftBoundary (q := q) x k)).1 := by
  let n := k - 1 + (q : ℤ)
  let m := k + (q : ℤ)
  let r := (S.outgoing (A.target (x.val n))).val
  let s := (S.outgoing (A.target (x.val m))).val
  have hr : S.source r = A.target (x.val n) := (S.outgoing _).property
  have hs : S.source s = A.target (x.val m) := (S.outgoing _).property
  have hp := K.left (fun i => x.val (k + (i : ℤ)))
    (fun i => S.backEdge x n r (q - (i + 1)))
    (fun i => S.backEdge x m s (q + 1 - (i + 1)))
    (fun i => S.backRun x n r (q - i))
    (fun i => S.backRun x m s (q + 1 - i))
    (by
      intro i hi
      have h := S.backRun_strip x n r hr q i hi
      have he : n - (q : ℤ) + (i : ℤ) + 1 = k + (i : ℤ) := by dsimp [n]; omega
      simpa only [he] using h)
    (by
      intro i hi
      have h := S.backRun_strip x m s hs (q + 1) i (by omega)
      have he : m - ((q + 1 : ℕ) : ℤ) + (i : ℤ) + 1 = k + (i : ℤ) := by
        dsimp [m]; omega
      simpa only [he] using h)
  have hm : m - (q : ℤ) = k := by dsimp [m]; omega
  simpa [leftBoundary, n, m, r, s, backRun, hm] using hp

def leftLift (x : History A) : S.FullSquare where
  left := x
  right := ⟨fun k => (S.back (x.val k) (S.leftBoundary (q := q) x k)).2, by
    intro k
    have h := S.back_spec (x.val k) (S.leftBoundary (q := q) x k)
      (S.leftBoundary_source x k).symm
    have h' := S.back_spec (x.val (k + 1)) (S.leftBoundary (q := q) x (k + 1))
      (S.leftBoundary_source x (k + 1)).symm
    have he : (S.back (x.val (k + 1)) (S.leftBoundary (q := q) x (k + 1))).1 =
        S.leftBoundary (q := q) x k := by
      have ht := S.leftBoundary_step K x (k + 1)
      simpa using ht.symm
    exact (S.endpoints h).2.2.2.symm.trans
      ((congrArg S.target he.symm).trans (S.endpoints h').2.1)⟩
  boundary := S.leftBoundary (q := q) x
  square k := by
    rw [S.leftBoundary_step K x k]
    exact S.back_spec _ _ (S.leftBoundary_source x k).symm

/-- The opposite lift is constructed, rather than postulated. -/
def rightBoundary (y : History B) (k : ℤ) : R :=
  S.forthRun y (k - (q : ℤ))
    (S.incoming (B.target (y.val (k - (q : ℤ))))).val q

theorem rightBoundary_target (y : History B) (k : ℤ) :
    S.target (S.rightBoundary (q := q) y k) = B.target (y.val k) := by
  have h := S.forthRun_target y (k - (q : ℤ))
    (S.incoming (B.target (y.val (k - (q : ℤ))))).val
    (S.incoming _).property q
  simpa [rightBoundary] using h

include K in
theorem rightBoundary_step (y : History B) (k : ℤ) :
    S.rightBoundary (q := q) y k =
      (S.forth (S.rightBoundary (q := q) y (k - 1)) (y.val k)).2 := by
  let n := k - (q : ℤ)
  let m := k - 1 - (q : ℤ)
  let r := (S.incoming (B.target (y.val n))).val
  let s := (S.incoming (B.target (y.val m))).val
  have hr : S.target r = B.target (y.val n) := (S.incoming _).property
  have hs : S.target s = B.target (y.val m) := (S.incoming _).property
  have hp := K.right
    (fun i => S.forthEdge y n r i)
    (fun i => S.forthEdge y m s (i + 1))
    (fun i => y.val (n + (i : ℤ) + 1))
    (fun i => S.forthRun y n r i)
    (fun i => S.forthRun y m s (i + 1))
    (by intro i hi; exact S.forthRun_square y n r hr i)
    (by
      intro i hi
      have h := S.forthRun_square y m s hs (i + 1)
      have he : m + ((i + 1 : ℕ) : ℤ) + 1 = n + (i : ℤ) + 1 := by
        dsimp [m, n]; omega
      simpa only [he] using h)
  have hm : m + (q : ℤ) + 1 = k := by dsimp [m]; omega
  simpa [rightBoundary, n, m, r, s, forthRun, hm] using hp

def rightLift (y : History B) : S.FullSquare where
  right := y
  left := ⟨fun k => (S.forth (S.rightBoundary (q := q) y (k - 1)) (y.val k)).1, by
    intro k
    have h := S.forth_spec (S.rightBoundary (q := q) y (k - 1)) (y.val k)
      ((S.rightBoundary_target y (k - 1)).trans (by simpa using y.property (k - 1)))
    have h' := S.forth_spec (S.rightBoundary (q := q) y k) (y.val (k + 1))
      ((S.rightBoundary_target y k).trans (y.property k))
    have he := S.rightBoundary_step K y k
    simpa using (S.endpoints h).2.2.1.symm.trans
      ((congrArg S.source he.symm).trans (S.endpoints h').1)⟩
  boundary := S.rightBoundary (q := q) y
  square k := by
    rw [S.rightBoundary_step K y k]
    exact S.forth_spec _ _ ((S.rightBoundary_target y (k - 1)).trans
      (by simpa using y.property (k - 1)))

include K in
/-- Equality of entire lifts is a CONSEQUENCE of left q-step forgetting. -/
theorem full_left_unique (P Q : S.FullSquare) (hx : P.left = Q.left) :
    P.boundary = Q.boundary ∧ P.right = Q.right := by
  have hb : P.boundary = Q.boundary := by
    funext k
    have h := K.left
      (fun i => P.left.val (k + (i : ℤ) + 1))
      (fun i => P.right.val (k + (i : ℤ) + 1))
      (fun i => Q.right.val (k + (i : ℤ) + 1))
      (fun i => P.boundary (k + (i : ℤ)))
      (fun i => Q.boundary (k + (i : ℤ)))
      (by
        intro i hi
        have h := P.square (k + (i : ℤ) + 1)
        have hk : k + (i : ℤ) + 1 - 1 = k + (i : ℤ) := by omega
        rw [hk] at h
        simpa [Int.natCast_add, add_assoc] using h)
      (by
        intro i hi
        have h := Q.square (k + (i : ℤ) + 1)
        have hk : k + (i : ℤ) + 1 - 1 = k + (i : ℤ) := by omega
        rw [hk] at h
        simpa [hx, Int.natCast_add, add_assoc] using h)
    simpa using h
  refine ⟨hb, ?_⟩
  apply Subtype.ext
  funext k
  have hQ := Q.square k
  rw [← hx, ← hb] at hQ
  exact (S.back_unique (P.square k) hQ).2

include K in
theorem full_right_unique (P Q : S.FullSquare) (hy : P.right = Q.right) :
    P.boundary = Q.boundary ∧ P.left = Q.left := by
  have hb : P.boundary = Q.boundary := by
    funext k
    have h := K.right
      (fun i => P.left.val (k - (q : ℤ) + (i : ℤ) + 1))
      (fun i => Q.left.val (k - (q : ℤ) + (i : ℤ) + 1))
      (fun i => P.right.val (k - (q : ℤ) + (i : ℤ) + 1))
      (fun i => P.boundary (k - (q : ℤ) + (i : ℤ)))
      (fun i => Q.boundary (k - (q : ℤ) + (i : ℤ)))
      (by
        intro i hi
        have h := P.square (k - (q : ℤ) + (i : ℤ) + 1)
        have hk : k - (q : ℤ) + (i : ℤ) + 1 - 1 = k - (q : ℤ) + (i : ℤ) := by omega
        rw [hk] at h
        simpa [Int.natCast_add, add_assoc] using h)
      (by
        intro i hi
        have h := Q.square (k - (q : ℤ) + (i : ℤ) + 1)
        have hk : k - (q : ℤ) + (i : ℤ) + 1 - 1 = k - (q : ℤ) + (i : ℤ) := by omega
        rw [hk] at h
        simpa [hy, Int.natCast_add, add_assoc] using h)
    simpa using h
  refine ⟨hb, ?_⟩
  apply Subtype.ext
  funext k
  have hQ := Q.square k
  rw [← hy, ← hb] at hQ
  exact (S.forth_unique (P.square k) hQ).1

def H (x : History A) : History B := (S.leftLift K x).right

def Hinv (y : History B) : History A := (S.rightLift K y).left

theorem H_of_full (P : S.FullSquare) : S.H K P.left = P.right :=
  (S.full_left_unique K (S.leftLift K P.left) P rfl).2

theorem Hinv_of_full (P : S.FullSquare) : S.Hinv K P.right = P.left :=
  (S.full_right_unique K (S.rightLift K P.right) P rfl).2

def historyEquiv : History A ≃ History B where
  toFun := S.H K
  invFun := S.Hinv K
  left_inv x := S.Hinv_of_full K (S.leftLift K x)
  right_inv y := S.H_of_full K (S.rightLift K y)

/-- The fixed LEFT past through edge n; every legal future is allowed. -/
def ray (S : Squares A B (R := R)) (x : History A) (n : ℤ) : Set (History A) :=
  {z | ∀ k, k ≤ n → z.val k = x.val k}

abbrev Out (x : History A) (n : ℤ) :=
  {r : R // S.source r = A.target (x.val n)}

/-- beta is the whole prescribed right past, evaluated by the actual backward
recursion from r at cut n. Its domain is the integers at or before n. -/
def beta (x : History A) (n : ℤ) (r : S.Out x n) (k : {k : ℤ // k ≤ n}) : D :=
  S.backEdge x n r.val (n - k.val).toNat

def betaRay (x : History A) (n : ℤ) (r : S.Out x n) : Set (History B) :=
  {y | ∀ k (hk : k ≤ n), y.val k = S.beta x n r ⟨k, hk⟩}

theorem beta_endpoint (x : History A) (n : ℤ) (r : S.Out x n) :
    B.target (S.beta x n r ⟨n, le_rfl⟩) = S.target r.val := by
  have hs := S.backRun_square x n r.val r.property 0
  simpa [beta, backRun] using (S.endpoints hs).2.2.2.symm

/-- Any full square over this left ray has exactly the prescribed backward
past with its OWN actual outgoing numbered R edge at cut n. -/
theorem full_past (x : History A) (n : ℤ) (P : S.FullSquare)
    (hx : P.left ∈ S.ray x n) (r : S.Out x n) (hr : P.boundary n = r.val) :
    P.right ∈ S.betaRay x n r := by
  have hb : ∀ d : ℕ, P.boundary (n - (d : ℤ)) = S.backRun x n r.val d := by
    intro d
    induction d with
    | zero => simpa [backRun] using hr
    | succ d ih =>
      have hp := P.square (n - (d : ℤ))
      rw [hx _ (by omega), ih] at hp
      have hs := S.backRun_square x n r.val r.property d
      have h := (S.back_unique hp hs).1
      have hi : n - ((d + 1 : ℕ) : ℤ) = n - (d : ℤ) - 1 := by omega
      simpa only [hi] using h
  intro k hk
  let d := (n - k).toNat
  have he : n - (d : ℤ) = k := by dsimp [d]; omega
  have hp := P.square k
  rw [hx k hk, ← he, hb d] at hp
  simpa only [beta, he] using
    (S.back_unique hp (S.backRun_square x n r.val r.property d)).2

/-- Splice boundaries at the SAME cut. For k>n the recursion consumes the
chosen arbitrary right future, one actual phi-inverse square at a time. -/
def spliceBoundary (x : History A) (n : ℤ) (r : S.Out x n) (y : History B) (k : ℤ) : R :=
  if k ≤ n then S.backRun x n r.val (n - k).toNat
  else S.forthRun y n r.val (k - n).toNat

def spliceLeft (x : History A) (n : ℤ) (r : S.Out x n) (y : History B) (k : ℤ) : E :=
  if k ≤ n then x.val k else S.forthEdge y n r.val (k - n - 1).toNat

theorem spliceBoundary_back (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (d : ℕ) :
    S.spliceBoundary x n r y (n - (d : ℤ)) = S.backRun x n r.val d := by
  have hi : n - (d : ℤ) ≤ n := by omega
  have hd : (n - (n - (d : ℤ))).toNat = d := by omega
  simp only [spliceBoundary, if_pos hi, hd]

theorem spliceBoundary_forth (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (d : ℕ) :
    S.spliceBoundary x n r y (n + (d : ℤ)) = S.forthRun y n r.val d := by
  cases d with
  | zero => simp [spliceBoundary, backRun, forthRun]
  | succ d =>
    have hi : ¬ n + ((d + 1 : ℕ) : ℤ) ≤ n := by omega
    have hd : (n + ((d + 1 : ℕ) : ℤ) - n).toNat = d + 1 := by omega
    simp only [spliceBoundary, if_neg hi, hd]

theorem splice_square (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (hy : y ∈ S.betaRay x n r) (k : ℤ) :
    S.sq (S.spliceBoundary x n r y (k - 1)) (S.spliceLeft x n r y k)
      (y.val k) (S.spliceBoundary x n r y k) := by
  by_cases hk : k ≤ n
  · let d := (n - k).toNat
    have he : n - (d : ℤ) = k := by dsimp [d]; omega
    have he' : n - ((d + 1 : ℕ) : ℤ) = k - 1 := by omega
    have hb := S.spliceBoundary_back x n r y d
    have hb' := S.spliceBoundary_back x n r y (d + 1)
    rw [he] at hb
    rw [he'] at hb'
    rw [hb, hb', spliceLeft, if_pos hk, hy k hk]
    simpa only [beta, he] using S.backRun_square x n r.val r.property d
  · have ht : S.target r.val = B.target (y.val n) := by
      rw [hy n le_rfl]
      exact (S.beta_endpoint x n r).symm
    let d := (k - n - 1).toNat
    have he : n + (d : ℤ) + 1 = k := by dsimp [d]; omega
    have he' : n + (d : ℤ) = k - 1 := by omega
    have he'' : n + ((d + 1 : ℕ) : ℤ) = k := by omega
    have hb := S.spliceBoundary_forth x n r y d
    have hb' := S.spliceBoundary_forth x n r y (d + 1)
    rw [he'] at hb
    rw [he''] at hb'
    rw [hb, hb', spliceLeft, if_neg hk]
    simpa only [he] using S.forthRun_square y n r.val ht d

def splice (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (hy : y ∈ S.betaRay x n r) : S.FullSquare where
  right := y
  left := ⟨S.spliceLeft x n r y, by
    intro k
    have h := S.endpoints (S.splice_square x n r y hy k)
    have h' := S.endpoints (S.splice_square x n r y hy (k + 1))
    have he : k + 1 - 1 = k := by omega
    rw [he] at h'
    exact h.2.2.1.symm.trans h'.1⟩
  boundary := S.spliceBoundary x n r y
  square := S.splice_square x n r y hy

theorem splice_past (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (hy : y ∈ S.betaRay x n r) :
    (S.splice x n r y hy).left ∈ S.ray x n := by
  intro k hk
  simp only [splice, spliceLeft, if_pos hk]

/-- Whole-ray reverse inclusion, quantified over EVERY full legal y. -/
theorem whole_ray_preimage (x : History A) (n : ℤ) (r : S.Out x n)
    (y : History B) (hy : y ∈ S.betaRay x n r) :
    ∃ z : History A, z ∈ S.ray x n ∧ S.H K z = y ∧
      (S.leftLift K z).boundary n = r.val := by
  let P := S.splice x n r y hy
  have hb := (S.full_left_unique K (S.leftLift K P.left) P rfl).1
  refine ⟨P.left, S.splice_past x n r y hy, S.H_of_full K P, ?_⟩
  rw [hb]
  change S.spliceBoundary x n r y n = r.val
  simpa [backRun] using S.spliceBoundary_back x n r y 0

/-- Same integer cut, one component for each ACTUAL outgoing numbered R edge. -/
theorem same_cut_whole_ray_image (x : History A) (n : ℤ) :
    S.H K '' S.ray x n = ⋃ r : S.Out x n, S.betaRay x n r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let P := S.leftLift K z
    let r : S.Out x n := ⟨P.boundary n, by
      have h := (S.endpoints (P.square n)).2.2.1
      exact h.trans (congrArg A.target (hz n le_rfl))⟩
    exact Set.mem_iUnion.mpr ⟨r, S.full_past x n P hz r rfl⟩
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    obtain ⟨z, hz, hH, _⟩ := S.whole_ray_preimage K x n r y hr
    exact ⟨z, hz, hH⟩

include K in
/-- Right q-step forgetting of the COMMON LAST q right edges proves
separation of the boundary indices. This does not use full-lift uniqueness. -/
theorem component_disjoint (x : History A) (n : ℤ)
    {r s : S.Out x n} (hrs : r ≠ s) :
    Disjoint (S.betaRay x n r) (S.betaRay x n s) := by
  rw [Set.disjoint_left]
  intro y hyr hys
  have h := K.right
    (fun i => x.val (n - (q : ℤ) + (i : ℤ) + 1))
    (fun i => x.val (n - (q : ℤ) + (i : ℤ) + 1))
    (fun i => y.val (n - (q : ℤ) + (i : ℤ) + 1))
    (fun i => S.backRun x n r.val (q - i))
    (fun i => S.backRun x n s.val (q - i))
    (by
      intro i hi
      have hk : n - (q : ℤ) + (i : ℤ) + 1 ≤ n := by omega
      have hd : (n - (n - (q : ℤ) + (i : ℤ) + 1)).toNat = q - (i + 1) := by omega
      rw [hyr _ hk]
      simpa only [beta, hd] using S.backRun_strip x n r.val r.property q i hi)
    (by
      intro i hi
      have hk : n - (q : ℤ) + (i : ℤ) + 1 ≤ n := by omega
      have hd : (n - (n - (q : ℤ) + (i : ℤ) + 1)).toNat = q - (i + 1) := by omega
      rw [hys _ hk]
      simpa only [beta, hd] using S.backRun_strip x n s.val s.property q i hi)
  apply hrs
  apply Subtype.ext
  simpa [backRun] using h


/- The local constructions also supply the ordinary product-topology map.
No new topology is assigned to the histories. -/
section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace D] [DiscreteTopology D]
  [TopologicalSpace R] [DiscreteTopology R]

lemma backRun_continuous (n : ℤ) (g : History A → R) (hg : Continuous g) (d : ℕ) :
    Continuous (fun x => S.backRun x n (g x) d) := by
  induction d with
  | zero => exact hg
  | succ d ih =>
    have hx : Continuous (fun x : History A => x.val (n - (d : ℤ))) :=
      (continuous_apply _).comp continuous_subtype_val
    exact continuous_fst.comp
      ((continuous_of_discreteTopology : Continuous (fun p : E × R => S.back p.1 p.2)).comp
        (hx.prodMk ih))

lemma forthRun_continuous (n : ℤ) (g : History B → R) (hg : Continuous g) (d : ℕ) :
    Continuous (fun y => S.forthRun y n (g y) d) := by
  induction d with
  | zero => exact hg
  | succ d ih =>
    have hy : Continuous (fun y : History B => y.val (n + (d : ℤ) + 1)) :=
      (continuous_apply _).comp continuous_subtype_val
    exact continuous_snd.comp
      ((continuous_of_discreteTopology : Continuous (fun p : R × D => S.forth p.1 p.2)).comp
        (ih.prodMk hy))

lemma leftBoundary_continuous (k : ℤ) :
    Continuous (fun x : History A => S.leftBoundary (q := q) x k) := by
  apply S.backRun_continuous (k + (q : ℤ))
  exact (continuous_of_discreteTopology :
    Continuous (fun e : E => (S.outgoing (A.target e)).val)).comp
      ((continuous_apply _).comp continuous_subtype_val)

lemma rightBoundary_continuous (k : ℤ) :
    Continuous (fun y : History B => S.rightBoundary (q := q) y k) := by
  apply S.forthRun_continuous (k - (q : ℤ))
  exact (continuous_of_discreteTopology :
    Continuous (fun d : D => (S.incoming (B.target d)).val)).comp
      ((continuous_apply _).comp continuous_subtype_val)

theorem H_continuous : Continuous (S.H K) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  have hx : Continuous (fun x : History A => x.val k) :=
    (continuous_apply k).comp continuous_subtype_val
  exact continuous_snd.comp
    ((continuous_of_discreteTopology : Continuous (fun p : E × R => S.back p.1 p.2)).comp
      (hx.prodMk (S.leftBoundary_continuous (q := q) k)))

theorem Hinv_continuous : Continuous (S.Hinv K) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  have hy : Continuous (fun y : History B => y.val k) :=
    (continuous_apply k).comp continuous_subtype_val
  exact continuous_fst.comp
    ((continuous_of_discreteTopology : Continuous (fun p : R × D => S.forth p.1 p.2)).comp
      ((S.rightBoundary_continuous (q := q) (k - 1)).prodMk hy))

def historyHomeomorph : History A ≃ₜ History B where
  toEquiv := S.historyEquiv K
  continuous_toFun := S.H_continuous K
  continuous_invFun := S.Hinv_continuous K

end Topology

namespace FullSquare

def shift (P : S.FullSquare) : S.FullSquare where
  left := FiniteWindowTableCriterion.shift A P.left
  right := FiniteWindowTableCriterion.shift B P.right
  boundary k := P.boundary (k + 1)
  square k := by
    simpa [FiniteWindowTableCriterion.shift] using P.square (k + 1)

end FullSquare

theorem H_shift (x : History A) :
    S.H K (FiniteWindowTableCriterion.shift A x) =
      FiniteWindowTableCriterion.shift B (S.H K x) :=
  S.H_of_full K (FullSquare.shift S (S.leftLift K x))

/- A beta is represented by a genuine full legal history. This section reuses
EssentialWordRealization's actual outgoing tails to fill a representative's
future. The image and reverse-inclusion theorems above allow EVERY future. -/
section RepresentedRays
variable [Fintype V] [Fintype D] [DecidableEq V]

def betaFull (hB : Essential B) (x : History A) (n : ℤ) (r : S.Out x n) : History B :=
  let e := outgoingChoice B hB (S.target r.val)
  ⟨fun k => if k ≤ n then S.backEdge x n r.val (n - k).toNat
    else forwardTail B hB e (k - n - 1).toNat, by
    intro k
    by_cases hk' : k + 1 ≤ n
    · have hk : k ≤ n := by omega
      let d := (n - (k + 1)).toNat
      have hd : (n - k).toNat = d + 1 := by dsimp [d]; omega
      have hs := S.backRun_square x n r.val r.property (d + 1)
      have ht := S.backRun_square x n r.val r.property d
      simpa only [if_pos hk, if_pos hk', hd] using
        (S.endpoints hs).2.2.2.symm.trans (S.endpoints ht).2.1
    · by_cases hk : k ≤ n
      · have he : k = n := by omega
        subst k
        have hnot : ¬ n + 1 ≤ n := by omega
        simpa [hnot, forwardTail, backRun, beta] using
          (S.beta_endpoint x n r).trans (outgoingChoice_source B hB (S.target r.val)).symm
      · have hnot' : ¬ k + 1 ≤ n := by omega
        let d := (k - n - 1).toNat
        have hd : (k + 1 - n - 1).toNat = d + 1 := by dsimp [d]; omega
        simpa only [if_neg hk, if_neg hnot', hd] using forwardTail_seam B hB e d⟩

theorem betaFull_past (hB : Essential B) (x : History A) (n : ℤ) (r : S.Out x n)
    (k : ℤ) (hk : k ≤ n) :
    (S.betaFull hB x n r).val k = S.beta x n r ⟨k, hk⟩ := by
  simp only [betaFull, if_pos hk, beta]

theorem betaRay_is_whole_ray (hB : Essential B) (x : History A) (n : ℤ) (r : S.Out x n) :
    S.betaRay x n r = {y : History B | ∀ k, k ≤ n →
      y.val k = (S.betaFull hB x n r).val k} := by
  ext y
  constructor
  · intro hy k hk
    exact (hy k hk).trans (S.betaFull_past hB x n r k hk).symm
  · intro hy k hk
    exact (hy k hk).trans (S.betaFull_past hB x n r k hk)

theorem betaFull_endpoint (hB : Essential B) (x : History A) (n : ℤ) (r : S.Out x n) :
    B.target ((S.betaFull hB x n r).val n) = S.target r.val := by
  rw [S.betaFull_past hB x n r n le_rfl]
  exact S.beta_endpoint x n r

/-- The literal union of whole rays based at FULL histories, through edge n.
Both the representative and all arbitrary future members are actual histories. -/
theorem same_cut_full_rays (hB : Essential B) (x : History A) (n : ℤ) :
    S.H K '' S.ray x n =
      ⋃ r : S.Out x n, {y : History B | ∀ k, k ≤ n →
        y.val k = (S.betaFull hB x n r).val k} := by
  rw [S.same_cut_whole_ray_image K x n]
  congr 1
  funext r
  exact S.betaRay_is_whole_ray hB x n r

end RepresentedRays

end Squares
end D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge

namespace D5.S3.ConceptDynamics.Coding.NumberedSameCutWholeRay

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph)
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge

universe u
variable {H : Type u} [Group H] [Fintype H] [DecidableEq H] {a : ℕ}

/-- Only local square data, with the ORIGINAL boundary endpoints. -/
structure NumberedData (M N C : GroupMat H a a) where
  squares : Squares (expandedGraph M) (expandedGraph N) (R := Edge C × H)
  source_exact : ∀ r, squares.source r = (expandedGraph C).source r
  target_exact : ∀ r, squares.target r = (expandedGraph C).target r

namespace NumberedData
variable {M N C : GroupMat H a a} (T : NumberedData M N C)
variable {q : ℕ} (K : FiniteForgetting T.squares q)

/-- The index is the full numbered R edge together with its absolute sign.
Neither the source nor the edge is an adjacency class. -/
abbrev ActualOut (T : NumberedData M N C) (alpha : History (expandedGraph M)) (n : ℤ) :=
  {r : Edge C × H // (expandedGraph C).source r = (expandedGraph M).target (alpha.val n)}

def outEquiv (alpha : History (expandedGraph M)) (n : ℤ) :
    T.ActualOut alpha n ≃ T.squares.Out alpha n where
  toFun r := ⟨r.val, (T.source_exact r.val).trans r.property⟩
  invFun r := ⟨r.val, (T.source_exact r.val).symm.trans r.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def beta (hN : Essential (expandedGraph N))
    (alpha : History (expandedGraph M)) (n : ℤ) (r : T.ActualOut alpha n) :
    History (expandedGraph N) :=
  T.squares.betaFull hN alpha n (T.outEquiv alpha n r)

def Cleft (T : NumberedData M N C) (alpha : History (expandedGraph M)) (n : ℤ) :
    Set (History (expandedGraph M)) := {x | ∀ k, k ≤ n → x.val k = alpha.val k}

def Cright (T : NumberedData M N C) (beta : History (expandedGraph N)) (n : ℤ) :
    Set (History (expandedGraph N)) := {y | ∀ k, k ≤ n → y.val k = beta.val k}

/-- H is the map actually CONSTRUCTED by q-square overlap, not supplied by
NumberedData. This conclusion uses every original edge and the same cut n. -/
theorem numbered_same_cut_whole_ray_image (hN : Essential (expandedGraph N))
    (alpha : History (expandedGraph M)) (n : ℤ) :
    T.squares.H K '' T.Cleft alpha n =
      ⋃ r : T.ActualOut alpha n, T.Cright (T.beta hN alpha n r) n := by
  have h := T.squares.same_cut_full_rays K hN alpha n
  ext y
  constructor
  · intro hy
    have hy' : y ∈ ⋃ s : T.squares.Out alpha n,
        {z : History (expandedGraph N) | ∀ k, k ≤ n →
          z.val k = (T.squares.betaFull hN alpha n s).val k} := h ▸ hy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy'
    refine Set.mem_iUnion.mpr ⟨(T.outEquiv alpha n).symm s, ?_⟩
    simpa [Cright, beta] using hs
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    have hy' : y ∈ ⋃ s : T.squares.Out alpha n,
        {z : History (expandedGraph N) | ∀ k, k ≤ n →
          z.val k = (T.squares.betaFull hN alpha n s).val k} :=
      Set.mem_iUnion.mpr ⟨T.outEquiv alpha n r, hr⟩
    exact h.symm ▸ hy'

/-- Literal target endpoint of the indexed numbered boundary edge. -/
theorem numbered_beta_endpoint (hN : Essential (expandedGraph N))
    (alpha : History (expandedGraph M)) (n : ℤ) (r : T.ActualOut alpha n) :
    (expandedGraph N).target ((T.beta hN alpha n r).val n) =
      (expandedGraph C).target r.val := by
  exact (T.squares.betaFull_endpoint hN alpha n (T.outEquiv alpha n r)).trans
    (T.target_exact r.val)

/-- Every arbitrary legal right future is consumed by the forward inverse
square recursion. The full lift has alpha as its exact left past and r at n. -/
theorem numbered_arbitrary_future_preimage (hN : Essential (expandedGraph N))
    (alpha : History (expandedGraph M)) (n : ℤ) (r : T.ActualOut alpha n)
    (y : History (expandedGraph N)) (hy : y ∈ T.Cright (T.beta hN alpha n r) n) :
    ∃ x : History (expandedGraph M), x ∈ T.Cleft alpha n ∧ T.squares.H K x = y ∧
      (T.squares.leftLift K x).boundary n = r.val := by
  have hp : y ∈ T.squares.betaRay alpha n (T.outEquiv alpha n r) := by
    rw [T.squares.betaRay_is_whole_ray hN alpha n (T.outEquiv alpha n r)]
    exact hy
  exact T.squares.whole_ray_preimage K alpha n (T.outEquiv alpha n r) y hp

include K in
/-- Exact numbered-edge disjointness from RIGHT q-step forgetting. -/
theorem numbered_components_disjoint (hN : Essential (expandedGraph N))
    (alpha : History (expandedGraph M)) (n : ℤ)
    {r s : T.ActualOut alpha n} (hrs : r ≠ s) :
    Disjoint (T.Cright (T.beta hN alpha n r) n) (T.Cright (T.beta hN alpha n s) n) := by
  have hrs' : T.outEquiv alpha n r ≠ T.outEquiv alpha n s :=
    fun h => hrs ((T.outEquiv alpha n).injective h)
  have hd := T.squares.component_disjoint K alpha n hrs'
  rw [T.squares.betaRay_is_whole_ray hN alpha n (T.outEquiv alpha n r),
    T.squares.betaRay_is_whole_ray hN alpha n (T.outEquiv alpha n s)] at hd
  exact hd

end NumberedData
end D5.S3.ConceptDynamics.Coding.NumberedSameCutWholeRay
