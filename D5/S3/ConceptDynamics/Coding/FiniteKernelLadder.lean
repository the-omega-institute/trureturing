/- GID: D5/S3/ConceptDynamics/Coding/FiniteKernelLadder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteKernelLadder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite kernel towers, original-length termination, cochain strips and stored endpoint coordinates. -/

import D5.S3.ConceptDynamics.Coding.FiniteKernelLadder.KernelReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnly.FiniteKernelLadder

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open SourceOnly.KernelRSSquare
open SourceOnly.KernelRSSquareGyration
open SourceOnly.UnitLagReduction

universe u

/-- An actual COLUMN elementary SSE. Its two equations are part of the
input word, not a shift-equivalence surrogate. -/
structure Edge (X Y : Based.{u}) where
  r : X.V →ₗ[D] Y.V
  s : Y.V →ₗ[D] X.V
  sr : s.comp r = X.time
  rs : r.comp s = Y.time

namespace Edge
variable {X Y : Based.{u}}

/-- The actual induced forward arrow on the simultaneous vertex quotients. -/
def reduceR (e : Edge X Y) : X.reduce.V →ₗ[D] Y.reduce.V :=
  (LinearMap.ker X.time).liftQ ((project Y.time).comp e.r) (by
    intro x hx
    apply (Y.project_zero_iff _).mpr
    have hc : Y.time (e.r x) = e.r (X.time x) := by
      rw [← e.rs, ← e.sr]
      rfl
    rw [hc]
    change X.time x = 0 at hx
    rw [hx, map_zero])

def reduceS (e : Edge X Y) : Y.reduce.V →ₗ[D] X.reduce.V :=
  (LinearMap.ker Y.time).liftQ ((project X.time).comp e.s) (by
    intro y hy
    apply (X.project_zero_iff _).mpr
    have hc : X.time (e.s y) = e.s (Y.time y) := by
      rw [← e.rs, ← e.sr]
      rfl
    rw [hc]
    change Y.time y = 0 at hy
    rw [hy, map_zero])

@[simp] theorem reduceR_project (e : Edge X Y) (x : X.V) :
    e.reduceR (project X.time x) = project Y.time (e.r x) := rfl

@[simp] theorem reduceS_project (e : Edge X Y) (y : Y.V) :
    e.reduceS (project Y.time y) = project X.time (e.s y) := rfl

/-- This pair IS the supplier's bottomForward/bottomBackward after the
two actual endpoint equations identify P,Q with the vertex dynamics. -/
def reduce (e : Edge X Y) : Edge X.reduce Y.reduce where
  r := e.reduceR
  s := e.reduceS
  sr := by
    ext z
    obtain ⟨x, rfl⟩ := (LinearMap.ker X.time).mkQ_surjective z
    change e.reduceS (e.reduceR (project X.time x)) =
      X.reduce.time (project X.time x)
    rw [reduceR_project, reduceS_project, Based.reduced_project]
    exact congrArg (project X.time) (congrArg (fun t => t x) e.sr)
  rs := by
    ext z
    obtain ⟨y, rfl⟩ := (LinearMap.ker Y.time).mkQ_surjective z
    change e.reduceR (e.reduceS (project Y.time y)) =
      Y.reduce.time (project Y.time y)
    rw [reduceS_project, reduceR_project, Based.reduced_project]
    exact congrArg (project Y.time) (congrArg (fun t => t y) e.rs)

def weight (d : ℕ) [NeZero d] (e : Edge X Y) : ZMod 3 :=
  value (d := d) X.basis Y.basis e.r e.s

/-- Four ACTUAL RS triangles, not just naturality of the quotient square.
The center basis is chosen once for this cell; vertex quotient bases are
those of Based.reduce and are reused by both adjacent cells. No coordinate
reset is inserted. Both vertical values are retained literally. -/
theorem cell {d : ℕ} [NeZero d] (hd : 3 ∣ d) (e : Edge X Y) :
    e.weight d + Y.vertical (d := d) =
      X.vertical (d := d) + e.reduce.weight d := by
  cases X with
  | @mk VX ax mx nx bx tx =>
    cases Y with
    | @mk VY ay my ny by_ ty =>
      letI := ax
      letI := mx
      letI := ay
      letI := my
      rcases e with ⟨r, s, hsr, hrs⟩
      change VX →ₗ[D] VY at r
      change VY →ₗ[D] VX at s
      change s.comp r = tx at hsr
      change r.comp s = ty at hrs
      cases hsr
      cases hrs
      let bc := dyadicQuotientBasis by_ r
      let X' : Based.{u} := { V := VX, dim := nx, basis := bx, time := s.comp r }
      let Y' : Based.{u} := { V := VY, dim := ny, basis := by_, time := r.comp s }
      exact kernel_square hd r s bx by_ bc.2 X'.quotientCoordinates.2
        Y'.quotientCoordinates.2

end Edge

/-- A finite arbitrary elementary word. Length zero is an actual constructor. -/
inductive Path : Based.{u} → Based.{u} → ℕ → Type (u+1)
  | nil (X : Based.{u}) : Path X X 0
  | cons {X Y Z : Based.{u}} {n : ℕ} (e : Edge X Y) (tail : Path Y Z n) :
      Path X Z (n+1)

namespace Path
variable {X Y Z : Based.{u}} {n m : ℕ}

def forward : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → X.V →ₗ[D] Y.V
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .cons e tail => tail.forward.comp e.r

def forwardRows (w : Path X Y n) : Mat X.dim Y.dim :=
  rows X.basis Y.basis w.forward

/-- The recursive sum of exactly the existing B_d on the actual letters. -/
def weight (d : ℕ) [NeZero d] :
    {X Y : Based.{u}} → {n : ℕ} → Path X Y n → ZMod 3
  | _, _, _, .nil _ => 0
  | _, _, _, .cons e tail => e.weight d + tail.weight d

@[simp] theorem forwardRows_nil (X : Based.{u}) : (nil X).forwardRows = 1 := rows_id _

/-- Explicit chronological order R_0 R_1 ... R_(n-1) in ROW coordinates. -/
theorem forwardRows_cons (e : Edge X Y) (tail : Path Y Z n) :
    (cons e tail).forwardRows = rows X.basis Y.basis e.r * tail.forwardRows :=
  rows_comp _ _ _ _ _


def reduce : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → Path X.reduce Y.reduce n
  | _, _, _, .nil X => .nil X.reduce
  | _, _, _, .cons e tail => .cons e.reduce tail.reduce

/-- Naturality of the actual chronological COLUMN composite. This theorem
is used for products only; the cochain proof instead consumes Edge.cell. -/
theorem reduce_forward (w : Path X Y n) :
    w.reduce.forward.comp (project X.time) = (project Y.time).comp w.forward := by
  induction w with
  | nil X => rfl
  | cons e tail ih =>
      ext x
      change tail.reduce.forward (e.reduceR (project _ x)) =
        project _ (tail.forward (e.r x))
      rw [Edge.reduceR_project]
      exact congrArg (fun t => t (e.r x)) ih

/-- Sum the strip, with BOTH endpoint vertical terms still visible.
Every interior vertical term cancels because its module AND basis are
literally the same on the two incident cells. -/
theorem strip {d : ℕ} [NeZero d] (hd : 3 ∣ d) (w : Path X Y n) :
    w.weight d + Y.vertical (d := d) =
      X.vertical (d := d) + w.reduce.weight d := by
  induction w with
  | nil X => simp only [weight, reduce, zero_add, add_zero]
  | @cons X Z Y n e tail ih =>
      change (e.weight d + tail.weight d) + _ = _ + (e.reduce.weight d + _)
      calc
        (e.weight d + tail.weight d) + Y.vertical (d := d) =
            e.weight d + (tail.weight d + Y.vertical (d := d)) := add_assoc _ _ _
        _ = e.weight d + (_ + tail.reduce.weight d) := by rw [ih]
        _ = (e.weight d + _) + tail.reduce.weight d := (add_assoc _ _ _).symm
        _ = (X.vertical (d := d) + e.reduce.weight d) + tail.reduce.weight d := by
          rw [e.cell hd]
        _ = X.vertical (d := d) + (e.reduce.weight d + tail.reduce.weight d) :=
          add_assoc _ _ _

/-- One complete row of cells preserves the same cochain for unit endpoints. -/
theorem reduce_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (w : Path X Y n) (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    w.reduce.weight d = w.weight d := by
  have h := w.strip hd
  rw [X.endpoint_vertical hd hX, Y.endpoint_vertical hd hY, add_zero, zero_add] at h
  exact h.symm

/-- Actual endpoint quotient bases give equality of chronological products,
not just conjugacy of their induced actions. HEq accounts for the rank
identity proved by the endpoint basis Sigma equality. -/
theorem reduce_forwardRows (w : Path X Y n)
    (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    HEq w.reduce.forwardRows w.forwardRows := by
  have hn := w.reduce_forward
  change HEq (rows X.quotientCoordinates.2 Y.quotientCoordinates.2 w.reduce.forward)
    (rows X.basis Y.basis w.forward)
  rw [X.endpoint_coordinates hX, Y.endpoint_coordinates hY]
  exact heq_of_eq (rows_transport X.basis Y.basis
    (X.projectEquiv (unit_injective hX.unit))
    (Y.projectEquiv (unit_injective hY.unit)) w.forward w.reduce.forward hn)

def stage (w : Path X Y n) : (j : ℕ) → Path (X.stage j) (Y.stage j) n
  | 0 => w
  | j+1 => (w.stage j).reduce

theorem stage_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (w : Path X Y n) (hX : IsUnit X.time) (hY : IsUnit Y.time) (j : ℕ) :
    (w.stage j).weight d = w.weight d := by
  induction j with
  | zero => rfl
  | succ j ih =>
      exact ((w.stage j).reduce_weight hd (X.stage_isUnit hX j)
        (Y.stage_isUnit hY j)).trans ih

theorem stage_forwardRows (w : Path X Y n)
    (hX : IsUnit X.time) (hY : IsUnit Y.time) (j : ℕ) :
    HEq (w.stage j).forwardRows w.forwardRows := by
  induction j with
  | zero => rfl
  | succ j ih =>
      exact HEq.trans ((w.stage j).reduce_forwardRows
        (X.stage_isUnit hX j) (Y.stage_isUnit hY j)) ih

/-- Membership of ALL vertices, including the last one. -/
def All (p : Based.{u} → Prop) : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → Prop
  | X, _, _, .nil _ => p X
  | X, _, _, .cons _ tail => p X ∧ tail.All p

theorem all_head {p : Based.{u} → Prop} (w : Path X Y n) (h : w.All p) : p X := by
  cases w with
  | nil X => exact h
  | cons e tail => exact h.1

theorem all_last {p : Based.{u} → Prop} (w : Path X Y n) (h : w.All p) : p Y := by
  revert h
  induction w with
  | nil X => exact fun h => h
  | cons e tail ih => exact fun h => ih h.2

theorem all_mono {p q : Based.{u} → Prop} (w : Path X Y n)
    (hpq : ∀ V, p V → q V) (h : w.All p) : w.All q := by
  revert h
  induction w with
  | nil X => exact fun h => hpq X h
  | cons e tail ih => exact fun h => ⟨hpq _ h.1, ih h.2⟩

theorem all_reduce {p : Based.{u} → Prop} (w : Path X Y n)
    (h : w.All (fun V => p V.reduce)) : w.reduce.All p := by
  revert h
  induction w with
  | nil X => exact fun h => h
  | cons e tail ih => exact fun h => ⟨h.1, ih h.2⟩

theorem all_stage {p : Based.{u} → Prop} (w : Path X Y n) (j : ℕ)
    (h : w.All (fun V => p (V.stage j))) : (w.stage j).All p := by
  revert h
  induction j generalizing p with
  | zero => exact fun h => h
  | succ j ih => exact fun h => (w.stage j).all_reduce (ih h)

/-- Ordinary concatenation, used to expose actual prefixes rather than
postulating lag data at each vertex. -/
def append : {X Y Z : Based.{u}} → {n m : ℕ} →
    Path X Y n → Path Y Z m → Path X Z (n+m)
  | _, _, _, _, _, .nil _, v => by simpa only [Nat.zero_add] using v
  | _, _, _, _, _, .cons e tail, v => by
      simpa only [Nat.add_right_comm] using cons e (append tail v)

/-- Every vertex is reached by an actual prefix of length at most n.
This retains arbitrary singular intermediates and the empty prefix. -/
theorem all_from_prefix {A B C : Based.{u}} {k l : ℕ}
    (v : Path A B k) (w : Path B C l) :
    w.All (fun T => ∃ i : ℕ, i ≤ k+l ∧ Nonempty (Path A T i)) := by
  induction w generalizing A k with
  | nil B => exact ⟨k, by omega, ⟨v⟩⟩
  | @cons B C E l e tail ih =>
      constructor
      · exact ⟨k, by omega, ⟨v⟩⟩
      · have ht := ih (v.append (.cons e (.nil C)))
        simpa only [Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 l] using ht

theorem all_prefix (w : Path X Y n) :
    w.All (fun T => ∃ k : ℕ, k ≤ n ∧ Nonempty (Path X T k)) := by
  simpa only [Nat.zero_add] using all_from_prefix (.nil X) w

/-- The exact immutable ExchangeChain; no new abstract lag premise. -/
theorem exchangeChain (w : Path X Y n) :
    D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain
      D X.matrix Y.matrix n := by
  induction w with
  | nil X => exact .nil X.matrix
  | @cons X Z Y n e tail ih =>
      have hsr : rows X.basis Z.basis e.r * rows Z.basis X.basis e.s = X.matrix := by
        rw [← rows_comp, e.sr]
        rfl
      have hrs : rows Z.basis X.basis e.s * rows X.basis Z.basis e.r = Z.matrix := by
        rw [← rows_comp, e.rs]
        rfl
      rw [← hrs] at ih
      have hc := D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.cons
        (rows X.basis Z.basis e.r) (rows Z.basis X.basis e.s) ih
      rw [hsr] at hc
      exact hc

/-- RectangularNilpotenceBarrier.exchange_chain_lag gives actual maps in COLUMN coordinates after
transposing back. All three consumed lag equations are proved here. -/
theorem lag (w : Path X Y n) :
    ∃ f : X.V →ₗ[D] Y.V, ∃ g : Y.V →ₗ[D] X.V,
      g.comp f = X.time^n ∧ f.comp g = Y.time^n ∧
      g.comp Y.time = X.time.comp g := by
  obtain ⟨F, G, _hAF, hBG, hFG, hGF⟩ :=
    D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.exchange_chain_lag w.exchangeChain
  let f := Matrix.toLin X.basis Y.basis F.transpose
  let g := Matrix.toLin Y.basis X.basis G.transpose
  have hf : rows X.basis Y.basis f = F := by
    simp only [rows, f, LinearMap.toMatrix_toLin, Matrix.transpose_transpose]
  have hg : rows Y.basis X.basis g = G := by
    simp only [rows, g, LinearMap.toMatrix_toLin, Matrix.transpose_transpose]
  refine ⟨f, g, ?_, ?_, ?_⟩
  · apply rows_injective X.basis X.basis
    rw [rows_comp, hf, hg, rows_pow]
    exact hFG
  · apply rows_injective Y.basis Y.basis
    rw [rows_comp, hf, hg, rows_pow]
    exact hGF
  · apply rows_injective Y.basis X.basis
    rw [rows_comp, rows_comp, hg]
    exact hBG

/-- All final maps are injective at K=n, from each actual prefix lag k≤n. -/
theorem final_all_injective (w : Path X Y n) (hX : IsUnit X.time) :
    (w.stage n).All (fun V => Function.Injective V.time) := by
  apply w.all_stage n
  apply w.all_mono _ w.all_prefix
  intro T hT
  obtain ⟨k, hk, ⟨pre⟩⟩ := hT
  obtain ⟨f, g, hgf, hfg, hgB⟩ := pre.lag
  exact T.final_injective hX.unit f g k n hk hgf hfg hgB

/-- Consumed logical helper for the vertex induction. -/
theorem all_mp {p q : Based.{u} → Prop} (w : Path X Y n) :
    w.All p → w.All (fun T => p T → q T) → w.All q := by
  induction w with
  | nil X => exact fun hi hp => hp hi
  | cons e tail ih => exact fun hi hp => ⟨hp.1 hi.1, ih hi.2 hp.2⟩

/-- Actual injective final vertices become units ONLY through their actual
finite prefix lag identities and unitFromLag. -/
theorem all_isUnit_of_all_injective (w : Path X Y n) (hX : IsUnit X.time)
    (hi : w.All (fun V => Function.Injective V.time)) :
    w.All (fun V => IsUnit V.time) := by
  have hp : w.All (fun T =>
      Function.Injective T.time → IsUnit T.time) := by
    apply w.all_mono _ w.all_prefix
    intro T hT hTinj
    obtain ⟨k, _hk, ⟨pre⟩⟩ := hT
    obtain ⟨f, g, hgf, hfg, hgB⟩ := pre.lag
    exact ⟨unitFromLag hX.unit T.time f g k hgf hfg hgB hTinj, rfl⟩
  exact w.all_mp hi hp

/-- This is the constructed final word's unit assertion, with no singular
intermediate of the original word ever being inverted. -/
theorem final_all_isUnit (w : Path X Y n) (hX : IsUnit X.time) :
    (w.stage n).All (fun V => IsUnit V.time) :=
  (w.stage n).all_isUnit_of_all_injective (X.stage_isUnit hX n)
    (w.final_all_injective hX)

end Path

namespace Based

/-- A Sigma packages a finite basis without losing its index equality. -/
def coordinates (X : Based.{u}) : Σ n : ℕ, Module.Basis (Fin n) D X.V :=
  ⟨X.dim, X.basis⟩

/-- FULL cumulative endpoint basis identity, not merely recursive pairwise
basis choices. It proves that the stored stage basis is the image of the
ORIGINAL basis under the ACTUAL q^j isomorphism. -/
theorem endpoint_basis_transport (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    (X.stage j).coordinates = ⟨X.dim, X.basis.map (X.qEquiv h j)⟩ := by
  induction j with
  | zero =>
      change (⟨X.dim, X.basis⟩ : Σ n, Module.Basis (Fin n) D X.V) = _
      congr 1
      ext i
      rfl
  | succ j ih =>
      let e := (X.stage j).projectEquiv (unit_injective (X.stage_isUnit h j).unit)
      let mapCoordinates :
          (Σ n, Module.Basis (Fin n) D (X.stage j).V) →
          (Σ n, Module.Basis (Fin n) D (X.stage (j+1)).V) :=
        fun c => ⟨c.1, c.2.map e⟩
      calc
        (X.stage (j+1)).coordinates = mapCoordinates (X.stage j).coordinates :=
          (X.stage j).endpoint_coordinates (X.stage_isUnit h j)
        _ = mapCoordinates ⟨X.dim, X.basis.map (X.qEquiv h j)⟩ := congrArg _ ih
        _ = ⟨X.dim, X.basis.map (X.qEquiv h (j+1))⟩ := by
          change (⟨X.dim, (X.basis.map (X.qEquiv h j)).map e⟩ :
            Σ n, Module.Basis (Fin n) D (X.stage (j+1)).V) = _
          congr 1
          ext i
          rfl

/-- The final time matrix is the literal original A, in that same basis. -/
theorem endpoint_matrix (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    HEq (X.stage j).matrix X.matrix := by
  change HEq (rows (X.stage j).coordinates.2 (X.stage j).coordinates.2
    (X.stage j).time) _
  rw [X.endpoint_basis_transport h j]
  exact heq_of_eq (rows_transport X.basis X.basis (X.qEquiv h j) (X.qEquiv h j)
    X.time (X.stage j).time (X.q_intertwines j))

abbrev unitVertex (X : Based.{u}) (h : IsUnit X.time) : SourceOnly.UnitWordGyration.Vertex where
  dim := X.dim
  time := rowUnit X.basis h.unit

end Based

/-- Consumed dependent-coordinate helper. HEq is used only to transport the
proved rank equality; the resulting vertices are literally equal. -/
theorem unitVertex_ext {A B : SourceOnly.UnitWordGyration.Vertex}
    (hdim : A.dim = B.dim)
    (hval : HEq (A.time : Mat A.dim A.dim) (B.time : Mat B.dim B.dim)) : A = B := by
  rcases A with ⟨na, a⟩
  rcases B with ⟨nb, b⟩
  dsimp only at hdim hval
  subst nb
  have hab : a = b := Units.ext (eq_of_heq hval)
  cases hab
  rfl

namespace Based

/-- This equality is at the exact UnitWordGyration vertex, not a new
cochain or a conjugate endpoint supplied as a premise. -/
theorem endpoint_unitVertex (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    (X.stage j).unitVertex (X.stage_isUnit h j) = X.unitVertex h := by
  apply unitVertex_ext
  · exact congrArg Sigma.fst (X.endpoint_basis_transport h j)
  · exact X.endpoint_matrix h j

end Based

namespace Edge
variable {X Y : Based.{u}}

/-- Reconstruct an existing ROW unit edge only after BOTH time units have
been proved. R and S are the same actual reduced linear maps in their
stored stage bases. -/
def unitEdge (e : Edge X Y) (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    SourceOnly.UnitWordGyration.Edge (X.unitVertex hX) (Y.unitVertex hY) where
  R := rows X.basis Y.basis e.r
  S := rows Y.basis X.basis e.s
  rs := by
    change rows X.basis Y.basis e.r * rows Y.basis X.basis e.s = X.matrix
    rw [← rows_comp, e.sr]
    rfl
  sr := by
    change rows Y.basis X.basis e.s * rows X.basis Y.basis e.r = Y.matrix
    rw [← rows_comp, e.rs]
    rfl

end Edge

namespace Path
variable {X Y : Based.{u}} {n : ℕ}

/-- Reconstruct the existing finite Word, with an actual unit at every
vertex. The hypotheses here are discharged by final_all_isUnit below. -/
def unitWord : {X Y : Based.{u}} → {n : ℕ} → (w : Path X Y n) →
    (h : w.All (fun V => IsUnit V.time)) →
    SourceOnly.UnitWordGyration.Word
      (X.unitVertex (w.all_head h)) (Y.unitVertex (w.all_last h))
  | _, _, _, .nil X, h => .nil (X.unitVertex h)
  | _, _, _, .cons e tail, h =>
      .cons (e.unitEdge h.1 (tail.all_head h.2)) (tail.unitWord h.2)

theorem unitWord_weight {d : ℕ} [NeZero d] (w : Path X Y n)
    (h : w.All (fun V => IsUnit V.time)) :
    (w.unitWord h).weight d = w.weight d := by
  revert h
  induction w with
  | nil X => exact fun _ => rfl
  | cons e tail ih =>
      intro h
      change e.weight d + (tail.unitWord h.2).weight d = e.weight d + tail.weight d
      rw [ih h.2]

/-- Literal chronological forward product, retained by reconstruction. -/
theorem unitWord_forward (w : Path X Y n)
    (h : w.All (fun V => IsUnit V.time)) :
    (w.unitWord h).forward = w.forwardRows := by
  revert h
  induction w with
  | nil X => exact fun _ => (forwardRows_nil X).symm
  | cons e tail ih =>
      intro h
      change rows _ _ e.r * (tail.unitWord h.2).forward = _
      rw [ih h.2, forwardRows_cons]

end Path

/-- Transport along the proved endpoint-vertex equality. This changes no
letter, basis, cochain value or forward matrix entry. -/
def transportLoop {A B : SourceOnly.UnitWordGyration.Vertex} (h : A = B)
    (w : SourceOnly.UnitWordGyration.Word A A) : SourceOnly.UnitWordGyration.Word B B :=
  h ▸ w

theorem transportLoop_weight {A B : SourceOnly.UnitWordGyration.Vertex}
    {d : ℕ} [NeZero d] (h : A = B) (w : SourceOnly.UnitWordGyration.Word A A) :
    (transportLoop h w).weight d = w.weight d := by
  cases h
  rfl

theorem transportLoop_forward {A B : SourceOnly.UnitWordGyration.Vertex}
    (h : A = B) (w : SourceOnly.UnitWordGyration.Word A A) :
    HEq (transportLoop h w).forward w.forward := by
  cases h
  rfl

/-- CLOSED arbitrary finite elementary loop-to-one-edge construction.
It returns the existing unit Word on the literal original row vertex, the
unit whose value is the actual chronological forward product, preservation
of the SAME B_d sum, and the existing loop_one_edge comparison.

No ladder, cochain conservation, quotient basis or intermediate unit is an
input. Length zero and rank zero are retained. The independent original-h
periodic/beam application is outside this finite algebraic statement. -/
theorem arbitrary_loop_one_edge {X : Based.{u}} {n : ℕ}
    (w : Path X X n) (hX : IsUnit X.time) :
    ∃ v : SourceOnly.UnitWordGyration.Word (X.unitVertex hX) (X.unitVertex hX),
    ∃ U : (Mat X.dim X.dim)ˣ,
      v.forward = w.forwardRows ∧
      (U : Mat X.dim X.dim) = w.forwardRows ∧
      Commute (U : Mat X.dim X.dim) X.matrix ∧
      ∀ (d : ℕ) [NeZero d], 3 ∣ d →
        v.weight d = w.weight d ∧
        w.weight d = dyadicGyration d w.forwardRows
          ((↑U⁻¹ : Mat X.dim X.dim) * X.matrix) := by
  have hu : (w.stage n).All (fun V => IsUnit V.time) := w.final_all_isUnit hX
  let v₀ := (w.stage n).unitWord hu
  have hv : (X.stage n).unitVertex ((w.stage n).all_head hu) = X.unitVertex hX :=
    X.endpoint_unitVertex hX n
  let v := transportLoop hv v₀
  have hforward : v.forward = w.forwardRows := by
    apply eq_of_heq
    exact HEq.trans (transportLoop_forward hv v₀)
      (HEq.trans (heq_of_eq ((w.stage n).unitWord_forward hu))
        (w.stage_forwardRows hX hX n))
  refine ⟨v, v.loopUnit, hforward, v.collapse_forward.trans hforward,
    v.loopUnit_commutes, ?_⟩
  intro d _ hd
  have hweight : v.weight d = w.weight d := by
    calc
      v.weight d = v₀.weight d := transportLoop_weight hv v₀
      _ = (w.stage n).weight d := (w.stage n).unitWord_weight hu
      _ = w.weight d := w.stage_weight hd hX hX n
  refine ⟨hweight, ?_⟩
  calc
    w.weight d = v.weight d := hweight.symm
    _ = dyadicGyration d v.forward
        ((v.loopUnit⁻¹).val * X.matrix) := v.loop_one_edge hd
    _ = _ := by rw [hforward]

end SourceOnly.FiniteKernelLadder

end -- close this source block's anonymous noncomputable section

