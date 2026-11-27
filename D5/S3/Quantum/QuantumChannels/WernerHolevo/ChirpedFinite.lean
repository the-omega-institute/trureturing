/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedFinite
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Input.constraints
   digest: Finite integer evaluation and chunking of chirped seed correlations and their derivatives. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ChirpedFinite

open scoped BigOperators

abbrev Gaussian := ℤ × ℤ
abbrev Dyadic := ℤ × ℤ

def scale : ℤ := 2 ^ 64
def radiusDen : ℤ := 2 ^ 30

def gmul (z w : Gaussian) : Gaussian :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def gconj (z : Gaussian) : Gaussian := (z.1, -z.2)
def gscale (a : ℤ) (z : Gaussian) : Gaussian := (a * z.1, a * z.2)

/-- The divisor at every call site is positive. Integer division is Euclidean. -/
def floorPair (z : Gaussian) (d : ℤ) : Gaussian := (z.1 / d, z.2 / d)

def taylorNumerator (a b : ℤ) (p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 12, (-1 : ℤ) ^ k *
    (((22 + p).factorial / (2 * k + p).factorial : ℕ) : ℤ) *
    a ^ (2 * k + p) * b ^ (22 + p - (2 * k + p))

def taylorDen (b : ℤ) (p : ℕ) : ℤ :=
  ((22 + p).factorial : ℤ) * b ^ (22 + p)

def taylorFloor (a b : ℤ) (p : ℕ) : ℤ :=
  scale * taylorNumerator a b p / taylorDen b p

def root (n j : ℕ) : Gaussian :=
  let a := 314159265358979323846 * (j : ℤ)
  let b := 4 * (n : ℤ) * (10 ^ 20)
  let square := fun z => floorPair (gmul z z) scale
  square (square (square (taylorFloor a b 0, taylorFloor a b 1)))

def dyadicNumerator (x : Dyadic) : ℤ := x.1 * 2 ^ x.2.toNat
def dyadicDenominator (x : Dyadic) : ℤ := 2 ^ (-x.2).toNat

theorem dyadicDenominator_pos (x : Dyadic) : 0 < dyadicDenominator x := by
  unfold dyadicDenominator
  positivity

def normalize (exponent : ℕ) (x : Dyadic) : ℤ :=
  x.1 * 2 ^ (x.2 + (exponent : ℤ)).toNat

def cayleyDen (x : Dyadic) : ℤ := dyadicNumerator x ^ 2 + dyadicDenominator x ^ 2

theorem cayleyDen_pos (x : Dyadic) : 0 < cayleyDen x :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (dyadicDenominator_pos x) _)

def cayley (x : Dyadic) (s : ℤ) : Gaussian × Gaussian :=
  let a := dyadicNumerator x
  let b := dyadicDenominator x
  let aa := a ^ 2
  let bb := b ^ 2
  let d := cayleyDen x
  (floorPair (gscale scale (s * (bb - aa), s * 2 * a * b)) d,
   floorPair (gscale scale (-s * 4 * (a * b) * bb, s * 2 * bb * (bb - aa))) (d ^ 2))

/-- Exact sums, with half-open consecutive intervals for the computational proofs. -/
def sumRange {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) : α :=
  ∑ i ∈ Finset.range n, f i

def sumWindow {α : Type*} [AddCommMonoid α] (first len : ℕ) (f : ℕ → α) : α :=
  sumRange len (fun j => f (first + j))

theorem sumRange_congr {α : Type*} [AddCommMonoid α] {n : ℕ} {f g : ℕ → α}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g :=
  Finset.sum_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))

theorem sumRange_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ) :
    sumRange (a + b) f = sumRange a f + sumWindow a b f :=
  Finset.sum_range_add f a b

theorem sumRange_fin {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ i : Fin n, f i.val) = sumRange n f :=
  (Finset.sum_range f).symm

def width : ℕ := 8

def chunkLen (n b : ℕ) : ℕ := if b < n / width then width else n % width

def sumChunks {α : Type*} [AddCommMonoid α] (n : ℕ) (part : ℕ → α) : α :=
  sumRange (n / width) part + part (n / width)

private theorem fullChunks {α : Type*} [AddCommMonoid α] (f : ℕ → α) (k : ℕ) :
    sumRange k (fun b => sumWindow (b * width) width f) = sumRange (k * width) f := by
  induction k with
  | zero => simp [sumRange]
  | succ k ih =>
    rw [sumRange, Finset.sum_range_succ]
    change sumRange k (fun b => sumWindow (b * width) width f) +
      sumWindow (k * width) width f = sumRange ((k + 1) * width) f
    rw [ih, Nat.succ_mul, sumRange_split f (k * width) width]

theorem sumChunks_eq {α : Type*} [AddCommMonoid α] (n : ℕ) (f part : ℕ → α)
    (h : ∀ b, b < n / width + 1 → part b = sumWindow (b * width) (chunkLen n b) f) :
    sumChunks n part = sumRange n f := by
  have hfull : sumRange (n / width) part =
      sumRange (n / width) (fun b => sumWindow (b * width) width f) :=
    sumRange_congr (fun b hb => by
      simpa only [chunkLen, if_pos hb] using h b (Nat.lt_succ_of_lt hb))
  have hlast := h (n / width) (Nat.lt_succ_self _)
  rw [chunkLen, if_neg (Nat.lt_irrefl _)] at hlast
  rw [sumChunks, hfull, fullChunks, hlast, ← sumRange_split]
  exact congrArg (fun k => sumRange k f) ((Nat.add_comm _ _).trans (Nat.mod_add_div' n width))

/-- Assemble adjacent checked intervals without re-evaluating their contents. -/
theorem coverNext {P : ℕ → Prop} (first len : ℕ)
    (previous : ∀ i, i < first → P i)
    (current : ∀ j : Fin len, P (first + j.val)) :
    ∀ i, i < first + len → P i := by
  intro i hi
  by_cases h : i < first
  · exact previous i h
  · have hc := current ⟨i - first, by omega⟩
    rwa [show first + (i - first) = i by omega] at hc

theorem coverStart {P : ℕ → Prop} {len : ℕ} (h : ∀ i : Fin len, P i.val) :
    ∀ i, i < len → P i := fun i hi => h ⟨i, hi⟩

theorem coverOne {P : ℕ → Prop} (first : ℕ)
    (previous : ∀ i, i < first → P i) (current : P first) :
    ∀ i, i < first + 1 → P i := by
  intro i hi
  by_cases h : i < first
  · exact previous i h
  · rwa [show i = first by omega]

theorem coverFirst {P : ℕ → Prop} (h : P 0) : ∀ i, i < 1 → P i := by
  intro i hi
  rwa [show i = 0 by omega]

/-- The nonzero orbits are emitted in increasing order of least element.
Each orbit is traversed using the original signed generators modulo n. -/
private def orbitVisit (n : ℕ) (generators : List ℤ) :
    ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, x :: todo, seen =>
    let (todo', seen') := generators.foldl (fun (acc : List ℕ × List ℕ) g =>
      let y := ((g * (x : ℤ)) % (n : ℤ)).toNat
      if acc.2.contains y then acc else (y :: acc.1, y :: acc.2)) (todo, seen)
    orbitVisit n generators fuel todo' seen'

def spectralOrbits (n : ℕ) (generators : List ℤ) : List (List ℕ) :=
  let (_, revOrbits) := ((List.range n).drop 1).foldl
    (fun (acc : List ℕ × List (List ℕ)) i =>
      if acc.1.contains i then acc
      else
        let seen := orbitVisit n generators n [i] [i]
        let sorted := ((List.range n).drop 1).filter (fun j => seen.contains j)
        (sorted ++ acc.1, sorted :: acc.2))
    ([], [])
  revOrbits.reverse

structure Chirp where
  phase : ℕ
  generators : List ℤ
  first : ℕ
  orbits : List (List ℕ)
  deriving DecidableEq, Inhabited

inductive Seed where
  | chirped (layout : Chirp)
  | constantSpectrum (parameter : ℕ)
  deriving DecidableEq, Inhabited

structure Constraint where
  left : ℕ
  power : ℕ
  right : ℕ
  includeImag : Bool
  deriving DecidableEq, Inhabited

def equationRows (constraints : List Constraint) : List (ℕ × Bool) :=
  (List.range constraints.length).map (fun j => (j, false)) ++
    ((List.range constraints.length).filter (fun j =>
      (constraints.getD j default).includeImag)).map (fun j => (j, true))

def component (imag : Bool) (z : Gaussian) : ℤ := if imag then z.2 else z.1

def chirpExponent (n : ℕ) (layout : Chirp) (d : ℕ) : ℕ :=
  ((n + 1) / 2) * layout.phase * d ^ 2

def coefficient (n : ℕ) (roots : ℕ → Gaussian) (e d : ℕ) (orbit : List ℕ) : Gaussian :=
  sumRange orbit.length (fun j => roots ((e + d * orbit.getD j 0) % n))

def seedValue (n : ℕ) (roots phases : ℕ → Gaussian) (d : ℕ) : Seed → Gaussian
  | .chirped layout =>
    let e := chirpExponent n layout d
    let base := gscale scale (roots (e % n))
    let terms := sumRange layout.orbits.length (fun j =>
      gmul (coefficient n roots e d (layout.orbits.getD j [])) (phases (layout.first + j)))
    floorPair (base + terms) ((n : ℤ) * scale)
  | .constantSpectrum j =>
    (if d = 0 then ((scale, 0) : Gaussian) else 0) +
      floorPair (phases j - (scale, 0)) (n : ℤ)

def seedSlope (n : ℕ) (roots slopes : ℕ → Gaussian) (d j : ℕ) : Seed → Gaussian
  | .chirped layout =>
    if layout.first ≤ j ∧ j < layout.first + layout.orbits.length then
      let e := chirpExponent n layout d
      let orbit := layout.orbits.getD (j - layout.first) []
      floorPair (gmul (coefficient n roots e d orbit) (slopes j)) ((n : ℤ) * scale)
    else 0
  | .constantSpectrum k =>
    if j = k then floorPair (slopes j) (n : ℤ) else 0

def leftColumn (n inv : ℕ) (c : Constraint) (d : ℕ) : ℕ :=
  ((inv ^ c.power) % n * d) % n

def corrTerm (n inv : ℕ) (c : Constraint) (v : ℕ → ℕ → Gaussian) (d : ℕ) : Gaussian :=
  gmul (gconj (v c.left (leftColumn n inv c d))) (v c.right d)

def jacTerm (n inv : ℕ) (c : Constraint) (v : ℕ → ℕ → Gaussian)
    (dv : ℕ → ℕ → ℕ → Gaussian) (j d : ℕ) : Gaussian :=
  let dl := leftColumn n inv c d
  gmul (gconj (dv c.left dl j)) (v c.right d) +
    gmul (gconj (v c.left dl)) (dv c.right d j)

def rowWeight (m : ℕ) (a : ℕ → ℕ → ℤ) (i : ℕ) : ℤ := sumRange m (fun j => |a i j|)

def stepRow (n m : ℕ) (a : ℕ → ℕ → ℤ) (f : ℕ → ℤ) (i : ℕ) : ℤ :=
  |sumRange m (fun j => a i j * f j)| + rowWeight m a i * (120 * (n : ℤ) * scale)

def defectTerm (h : ℤ) (m : ℕ) (a j : ℕ → ℕ → ℤ) (i k : ℕ) : ℤ :=
  |h * (if i = k then 1 else 0) - sumRange m (fun l => a i l * j l k)|

def defectRow (h : ℤ) (n m : ℕ) (a j : ℕ → ℕ → ℤ) (i : ℕ) : ℤ :=
  sumRange m (defectTerm h m a j i) + rowWeight m a i * (m : ℤ) * (420 * (n : ℤ) * scale)

def contraction (defect weight : ℤ) : ℤ :=
  defect + 16 * weight * (scale ^ 2 / radiusDen)

end ChirpedFinite
