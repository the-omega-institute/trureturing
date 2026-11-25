/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Core
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Kernel-evaluated enumeration, candidate filter and grouped prefix tests. -/

/-! Kernel-evaluated certificate primitives for smooth-predecessor prime tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- Fixed-point scale for products of `1 - 1 / q`. -/
def scale : Nat := 10 ^ 60

/-- Exponent cap used in the normalized sigma factor `σ(p^k)/p^k`. -/
def expCap : Nat := 60

/-- Odd primes at most `97`, in increasing order; a group label is an index into this list. -/
def oddPrimes : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- All primes at most `97`. -/
def allPrimes : List Nat := 2 :: oddPrimes

/-- Trial divisors used to discard composite successors. -/
def trialPrimes : List Nat := allPrimes

/-- Enumeration bound for predecessors `m = q - 1`. -/
def bound : Nat := 1000000

/-- Recursive power fold, stopping when the current argument exceeds `X`.
For `1 ≤ p`, it sums `f (c * p ^ e)` over `e < n` with `c * p ^ e ≤ X`. -/
noncomputable def powSum (n : Nat) : (Nat → Nat) → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => (Nat → Nat) → Nat → Nat → Nat → Nat) (fun _ _ _ _ => 0)
    (fun _ ih f p X c => if c ≤ X then f c + ih f p X (c * p) else 0) n

/-- Recursive weighted enumerator with each generator exponent truncated below `64`.
Its exact bounded-smooth-sum interpretation requires distinct prime generators,
a positive start or zero weight at zero, and the boundary and fuel conditions
in `smoothSum_eq_sum`.
The empty-list branch returns `w c` even when `X < c`. -/
noncomputable def smoothSum (w : Nat → Nat) (ps : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => w c)
    (fun p _ ih X c => powSum 64 (fun c' => ih X c') p X c) ps

/-- Nonzero powers of two. -/
def isPow2 (m : Nat) : Bool := m != 0 && (m &&& (m - 1)) == 0

/-- Necessary conditions for `m + 1` to be a non-Fermat odd prime with even predecessor `m`. -/
def candidate (m : Nat) : Bool :=
  m % 2 == 0 && !isPow2 m && 2 ^ m % (m + 1) == 1 &&
    trialPrimes.all (fun d => decide (m + 1 ≤ d) || (m + 1) % d != 0)

/-- Divide by `p` when divisible, for at most `n` recursive steps. -/
noncomputable def strip (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ m => m)
    (fun _ ih p m => if m % p == 0 then ih p (m / p) else m) n

/-- Repeated-division recognition with `64` division steps per generator.
For a list of primes, zeros and ones and `m < 2 ^ 65`, `isSmooth_iff` identifies the result
with membership in `Nat.factoredNumbers ps.toFinset`, including the zero case. -/
noncomputable def isSmooth (ps : List Nat) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun m => m == 1)
    (fun p _ ih m => ih (strip 64 p m)) ps m

/-- Strictly increasing values, each larger than `prev`. -/
noncomputable def increasingFrom (prev : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih prev => decide (prev < a) && ih a) l prev

/-- Table entry `q * 256 + i` labels `q` by `oddPrimes[i]`. -/
def entryValue (e : Nat) : Nat := e / 256

/-- Group index of a table entry. -/
def entryLabel (e : Nat) : Nat := e % 256

/-- A table entry is a labelled candidate whose predecessor is `97`-smooth and at most `bound`. -/
noncomputable def validEntry (e : Nat) : Bool :=
  match oddPrimes[entryLabel e]? with
  | some p =>
    decide (2 ≤ entryValue e) && decide (entryValue e - 1 ≤ bound) &&
      candidate (entryValue e - 1) && isSmooth allPrimes (entryValue e - 1) &&
      (entryValue e - 1) % p == 0
  | none => false

/-- Tail constants of a label `p`: `∏_{r ≤ p} r`, `∏_{r ≤ p} (r - 1)` and the floor sum
of `scale / (2 p m')` from the generators retained in `allPrimes.filter (· ≤ p)`. -/
noncomputable def tailData (p : Nat) : Nat × Nat × Nat :=
  let rs := allPrimes.filter (· ≤ p)
  (rs.foldl (· * ·) 1, rs.foldl (fun a r => a * (r - 1)) 1,
    smoothSum (fun c => scale / (2 * p * c)) rs (bound / (2 * p)) 1)

/-- Prefix tests with exponents `min j expCap` and `min (j + 1) expCap`.
They compare the fixed-point product with the truncated geometric factors. -/
def prefixOk (p j L : Nat) (t : Nat × Nat × Nat) : Bool :=
  let num := t.1
  let den := t.2.1
  let fs := t.2.2
  let k0 := min j expCap
  let k1 := min (j + 1) expCap
  let tailNum := den * 2 * p * scale + fs * den * 2 * p
  (j == 0 || decide (scale * (p - 1) * p ^ k0 ≤ (p ^ (k0 + 1) - 1) * L)) &&
    decide (num * scale ≤ tailNum) &&
    decide (scale * (p - 1) * p ^ k1 * (den * 2 * p * scale) ≤
      (p ^ (k1 + 1) - 1) * L * (tailNum - num * scale))

/-- Process table entries, updating `(count, fixed-point product)` of each group. -/
noncomputable def stepTable (tails : List (Nat × Nat × Nat)) (es : List Nat) :
    List (Nat × Nat) → Option (List (Nat × Nat)) :=
  List.rec (motive := fun _ => List (Nat × Nat) → Option (List (Nat × Nat))) (fun st => some st)
    (fun e _ ih st =>
      match oddPrimes[entryLabel e]?, st[entryLabel e]?, tails[entryLabel e]? with
      | some p, some (j, L), some t =>
        if prefixOk p j L t then
          ih (st.set (entryLabel e) (j + 1, L * (entryValue e - 1) / entryValue e))
        else none
      | _, _, _ => none) es

/-- Prefix tests at the indices simultaneously present in `oddPrimes`, `st` and `tails`.
Only their common zipped prefix is checked; empty inputs can pass. -/
def finalOk (tails : List (Nat × Nat × Nat)) (st : List (Nat × Nat)) : Bool :=
  (oddPrimes.zip (st.zip tails)).all fun x => prefixOk x.1 x.2.1.1 x.2.1.2 x.2.2

/-- Initial group states. -/
def initialState : List (Nat × Nat) := oddPrimes.map fun _ => (0, scale)

/-- Weight counting candidate predecessors. -/
def candidateWeight (m : Nat) : Nat := if candidate m then 1 else 0

/-- Tail constants of the labels, in the order of `oddPrimes`. -/
def tails : List (Nat × Nat × Nat) :=
  [(6,
    2,
    499982194655508726068604040711951091466409253331978526308600),
   (30,
    8,
    374918474524801766858879913292350420836932039492624769259308),
   (210,
    48,
    312268614397586783577630032340084265288313321840841796341569),
   (2310,
    480,
    218320565952179755109473358210546676322366047060796827361585),
   (30030,
    5760,
    199795208020979456383736005436186398464206134684251899627549),
   (510510,
    92160,
    161899835927672115688865396237431787044000307998858481304868),
   (9699690,
    1658880,
    152462748535518050096646444992278923127792709553562343731384),
   (223092870,
    36495360,
    131142421155029410091008207949552288839473786874227893257187),
   (6469693230,
    1021870080,
    107168603719001850260950937117682469628980516640058764662283),
   (200560490130,
    30656102400,
    103161685957678536906876956696157321764725549558101534379957),
   (7420738134810,
    1103619686400,
    88299070615766838195992512581100869777917970129211129110063),
   (304250263527210,
    44144787456000,
    81231498772309940861297362274534545922078574129471928810965),
   (13082761331670030,
    1854081073152000,
    78906283929103466742138725052793466633443421470562267466014),
   (614889782588491410,
    85287729364992000,
    73324937661936426405455097705116881825530059740441390432973),
   (32589158477190044730,
    4434961926979584000,
    65822305595888325738301437640983981990325199682577187929545),
   (1922760350154212639070,
    257227791764815872000,
    59737113329310699287074811223742054094457935213077354986261),
   (117288381359406970983270,
    15433667505888952320000,
    58441251714866851255601601034419180275050197472221043542594),
   (7858321551080267055879090,
    1018622055388670853120000,
    53638548598030801199404316187275314487416920813374086164165),
   (557940830126698960967415390,
    71303543877206959718400000,
    51031981138143253737019940675194745047170299865785210674478),
   (40729680599249024150621323470,
    5133855159158901099724800000,
    50063080829469894727089520777808261408572936361091407714766),
   (3217644767340672907899084554130,
    400440702414394285778534400000,
    46529897084962912942510984554609393908907409934019722587228),
   (267064515689275851355624017992790,
    32836137597980331433839820800000,
    44556402024503303076216976126431285795059263203461866471227),
   (23768741896345550770650537601358310,
    2889580108622269166177904230400000,
    41737003697664867148969769196080733326896604621922974515842),
   (2305567963945518424753102147331756070,
    277399690427737839953078806118400000,
    38398064980938103684855254586940121792552064007004380110424)]

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
