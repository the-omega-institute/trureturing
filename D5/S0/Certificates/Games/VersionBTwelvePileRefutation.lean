/- GID: D5/S0/Certificates/Games/VersionBTwelvePileRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/VersionBTwelvePileRefutation
   mirror-E: none(waiver:kernel-checked-finite-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Games/VersionBTwelvePileRefutation.PredictedClassification; result=D5/S0/Certificates/Games/VersionBTwelvePileRefutation.predicted_classification_refuted; claim=D5/S0/Certificates/Games/VersionBTwelvePileRefutation.PredictedClassification
   digest: Six piles of five and six piles of six lose in normal-play Version B, refuting the explicitly stated next-player prediction. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# A twelve-pile counterexample for Version B

A position records the multiplicities of positive pile sizes 1 through 6.
There is no bound on the number of piles in the game definition. This is the
closed subgame of the multiset game in which no pile exceeds 6: either legal
move only decreases pile sizes, so starting here cannot leave this subgame.
Zero-sized piles disappear, and the empty position has no move.

Library-first search: D5 was searched for take-away and impartial games;
the pinned Mathlib was searched for SetTheory/Game, PGame and impartial APIs.
None was found (Order/GameAdd concerns order relations, not this game).
We reuse Mathlib's list and well-founded induction infrastructure.

The arXiv abstract page for 2605.23213 was unreachable (DNS resolution failed).
We do NOT quote the paper. The explicit hypothesis tested here is: for k
nonempty piles, if every size is strictly greater than ceil(k/3) and the
number of odd piles is even, the position is a next-player win (not Losing).
`PredictedClassification` states exactly that implication on this closed
subgame. No claim about the paper's wording or verification frontier is
needed by the proof.

The certificate domain S consists of all six nonnegative counts summing to
at most 12, including zero. An independent Python sweep found 18564 states,
6005 losing states and a losing target. The certificate uses a single Nat:
its bit index is the dense stars-and-bars combinatorial rank of the counts.
This improves on fixed radix 13 by using 18564 bits rather than millions;
no rank-injectivity assumption is needed for soundness. The kernel checks the
entire local recurrence, then induction on tokens identifies the certificate
with Losing. The new computational witness is this checked recurrence; its
consumer is target_losing, which in turn proves the stated refutation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Games.VersionBTwelvePileRefutation

/-- Multiplicities of pile sizes 1, 2, 3, 4, 5 and 6, respectively. -/
abbrev Position := Nat × Nat × Nat × Nat × Nat × Nat

/-- Number of nonempty piles. -/
def pileCount : Position → Nat
  | ⟨a, b, c, d, e, f⟩ => a + b + c + d + e + f

/-- Total number of tokens, the well-founded measure. -/
def tokens : Position → Nat
  | ⟨a, b, c, d, e, f⟩ => a + 2*b + 3*c + 4*d + 5*e + 6*f

/-- Successors obtained by removing one token from exactly one nonempty pile. -/
def singleSuccessors : Position → List Position
  | ⟨a, b, c, d, e, f⟩ =>
    (if a = 0 then [] else [⟨a-1,b,c,d,e,f⟩]) ++
    (if b = 0 then [] else [⟨a+1,b-1,c,d,e,f⟩]) ++
    (if c = 0 then [] else [⟨a,b+1,c-1,d,e,f⟩]) ++
    (if d = 0 then [] else [⟨a,b,c+1,d-1,e,f⟩]) ++
    (if e = 0 then [] else [⟨a,b,c,d+1,e-1,f⟩]) ++
    (if f = 0 then [] else [⟨a,b,c,d,e+1,f-1⟩])

/-- Removing one token from every nonempty pile; size-one piles disappear. -/
def allSuccessor : Position → Position
  | ⟨_, b, c, d, e, f⟩ => ⟨b,c,d,e,f,0⟩

/-- The first legal move relation. -/
def SingleMove (s t : Position) : Prop := t ∈ singleSuccessors s

/-- The simultaneous move is legal only in a nonempty position. -/
def AllMove (s t : Position) : Prop := pileCount s ≠ 0 ∧ t = allSuccessor s

/-- Either kind of legal move. -/
def Move (s t : Position) : Prop := SingleMove s t ∨ AllMove s t

private theorem single_properties {s t : Position} (h : SingleMove s t) :
    tokens t < tokens s ∧ pileCount t ≤ pileCount s := by
  rcases s with ⟨a,b,c,d,e,f⟩
  simp only [SingleMove, singleSuccessors, List.mem_append, List.mem_ite_nil_left,
    List.mem_singleton, or_assoc] at h
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h, rfl⟩ <;> simp only [tokens, pileCount] <;> omega

/-- Every move strictly reduces the token count. -/
theorem move_decreases {s t : Position} (h : Move s t) : tokens t < tokens s := by
  rcases h with h | ⟨hne, rfl⟩
  · exact (single_properties h).1
  · rcases s with ⟨a,b,c,d,e,f⟩
    simp only [pileCount] at hne
    simp only [tokens, allSuccessor]
    omega

private theorem move_pileCount_le {s t : Position} (h : Move s t) :
    pileCount t ≤ pileCount s := by
  rcases h with h | ⟨_, rfl⟩
  · exact (single_properties h).2
  · rcases s with ⟨a,b,c,d,e,f⟩
    simp only [pileCount, allSuccessor]
    omega

/-- Previous-player win in normal play: every legal successor is not losing.
This well-founded recursion includes the empty position as a loss. -/
def Losing (s : Position) : Prop := ∀ t, Move s t → ¬ Losing t
termination_by tokens s
decreasing_by exact move_decreases ‹Move s t›

/-- The recursive normal-play characterization. -/
theorem losing_iff (s : Position) : Losing s ↔ ∀ t, Move s t → ¬ Losing t := by
  rw [Losing]

/-- The empty position is losing for the player to move. -/
theorem empty_losing : Losing ⟨0,0,0,0,0,0⟩ := by
  rw [losing_iff]
  simp [Move, SingleMove, AllMove, singleSuccessors, pileCount]

private def successors (s : Position) : List Position :=
  singleSuccessors s ++ if pileCount s = 0 then [] else [allSuccessor s]

private theorem mem_successors (s t : Position) : t ∈ successors s ↔ Move s t := by
  simp [successors, Move, SingleMove, AllMove]

-- Multiplicative binomial calculation, avoiding Pascal-tree reduction.
private def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | n, k+1 => n * binomial (n-1) k / (k+1)

private def rank : Position → Nat
  | ⟨a,b,c,d,e,f⟩ => a + binomial (a+b+1) 2 + binomial (a+b+c+2) 3 +
    binomial (a+b+c+d+3) 4 + binomial (a+b+c+d+e+4) 5 +
    binomial (a+b+c+d+e+f+5) 6

private def losingBits : Nat := 0x2aa80000055400aa0150284aaa00000aa805502a14d5500000aaa9552a4aaaa8000000002aa01540a852aaa9552a5540a852aa952a852a952a00000155002a80540a1000002aa01540a852000015552aa5495400000000001540a852a9552a40542952a414a4400155002a80540a10015500aa05429002aaa554a900000000055aab56aaa54ab56aa56aaaa005500a8142aa805502a14aaaa554a900000000150a54a9052910015402a050802a8150a552aa548000000001420115402a050aa8150a55028550a400a4402a05080a8520508290895028550a542a540a1052112854a844a5550000055402a8150a6aa800005554aa952555540000000015500aa054295554aa952aa05429554a9542954a950000055402a8150a400002aaa554a92a800000000002a8150a552aa5480a852a5482948800aa805502a148015552aa548000000002ad55ab5552a55ab552b56aa01540a852aaa9552a400000000542952a414a4401540a852a9552a4000000000a1009540a852a8142a852005220542902841484550a542a542908a952d5500000aaa9552a4aaaa8000000002aa01540a852aaa9552a5540a852aa952a852a952a000015552aa5495400000000001540a852a9552a40542952a414a4400aa0150284000000000ab556ad554a956ad54ad55554aa952000000002a14a9520a52254aa95200000028404040540a1542950a95050814884a152a2129555500000000055402a8150a55552aa54aa8150a5552a550a552a5554aaa9552a401540a852a9552a40542952a414a4400000000156aad5aaa952ad5aa95aa0000001556ad52a556a540281005080808150a542a542908a952d5402a8150a55552aa54aa8150a5552a550a552a5402a8150a552aa5480a852a5482948aad55ab5552a55ab552b540a852050829088000000002854aa44a5554aa952aa05429554a9542954a9554aa95202a14a9520a522554a9542954a9552a414a44000000212a8150a5552a550a552a540a852a5482948aa14aa54a852915229554a9542954a9552a414a44a952a910aa14aa54a8529152a554a9548954a955555554aa8015402a050aaad555500aa0542955554aa02a05095500aa054295554aa952aa05429554a9542954a95554aa8015402a050aaaaa805502a14aa9540540a1002a8150a552aa5480a852a5482948955002a80540a155402a8150a6a80540a12a8150a40000150a400a4400aa015028401540a85202a0508aa952000156a54aa0150285540a85200000ad5aa95aa015028405429028414a44a8142a852a152a05082908942a54225555aaaaa01540a852aaaa9540540a12aa01540a852aaa9552a5540a852aa952a852a952b5555402a8150a554aa02a050801540a852a9552a40542952a414a455500aa05429aa0150284aa054290000054290029100aa054290150284554a90000ab52aaa054290000056ad54ad502a1481420a522a852a152a148454a9555552a80a814255402a8150a55552aa54aa8150a5552a550a552a5554aa02a050801540a852a9552a40542952a414a455402a0509540a85200000a8520052202a0508aa952000156a5400000ad5aa95aa05082908952a5422555402a8150a55552aa54aa8150a5552a550a552a5402a8150a552aa5480a852a5482948aa8150a40000150a400a46a0508a04284422b56aa56a8521152a55554aa952aa05429554a9542954a9554aa95202a14a9520a522540a1542950a9552a556a54a95aa114aa8150a5552a550a552a540a852a5482948aa14aa54a852915aa5554a9542954a9552a414a44a952a912aa14aa54a8529152a554a9548954a9552aa000015402a05095500005502a14d540002aa549555000002a8150a5552a550a552a5400002a80540a100002a8150a40002aa54950000000a852a5482948800aa015028401540a85201552a400000ad5aa95aaaa0150285540a852aa952000014a4401502840542952a400008a8142a852a152205082908942a542252aa0000aa05429aa8000554a92aaa000005502a14aaa54aa14aa54a80002a8150a40002aa54950000000a852a5482948802a8150a402aa548000015ab552b56a8150a5552a40000294880a852a54800012a14a85488521152a5aa8000554a92aaa000005502a14aaa54aa14aa54a8000554a92a000000150a54a90529100a8142000002b56aa56aaaa5480000529129520004050a951094aaa800001540a852aa952a852a952aa9552a40542952a414a4400000ad5aa95aa0002ad4a810102952d502a14aaa54aa14aa54a8150a54a90529156ad54ad50a4220014aa952a852a952aa5482948952a55220542954a950a522a54aa952a912a952aaaaaa95402a050aab55540a852aaa950509540a852aa952a852a952aaa5500a8142aaaa0542954a828402a14a9520a5225500a8142aa05429a814254290029100a814202a1482845480a540a15429002d5028414844a152a112aab55540a852aaa950509540a852aa952a852a952b55540a852a9505080542952a414a45540a85350284a85200522054290508a901550a400b542908a952aaaa541425502a14aaa54aa14aa54aaa541420150a54a905291540a12a148014882845480a002d50895540a852aa952a852a952a0542952a414a4550a400a4684422d52aaa54aa14aa54aa9520a52250a954a9550a552a542948a952aa54aa44aa54aa9540002a05095400150a6a8005495500150a552a540002a050800150a4002a4a0002948802a05080a852054800b555028550a5520080a1052902854a844a550005429aa0015255400542954a950005429000a928000a52202a148152002d5a852a900414a414a96a8005495500150a552a54002a4a000294881420016aaa401240a55400542954a9552a414a44005aa0506a14aa54a852915aa454a9548954a9555554a8142ab55429554a2542954a9554a8142aaa14a9440a522540a15429a1291028414888a1522112aad550a55528950a552a56aa852a5102948aa14d0948852225225554a2542954a95528814a4542522220aa14aa54a85291523154a9548954a9552a0014254014d40254295000a1002900902028414842a1528112950053500950a540148048105210d285a804a852a0120420a150a5522152a555552855aa552a554a1552912854c844aad52a952b54a454c9552a5522952a554a012834280408044a50685040b4281554ad54a956ad552140aab

private def marked (s : Position) : Bool := losingBits.testBit (rank s)

private def check (s : Position) : Bool :=
  marked s == (successors s).all (fun t => !marked t)

private theorem certificate_checked :
    ∀ (a : Fin 13) (b : Fin (13-a.val)) (c : Fin (13-a.val-b.val))
      (d : Fin (13-a.val-b.val-c.val)) (e : Fin (13-a.val-b.val-c.val-d.val))
      (f : Fin (13-a.val-b.val-c.val-d.val-e.val)),
      check ⟨a.val,b.val,c.val,d.val,e.val,f.val⟩ = true := by
  decide +kernel

private theorem certificate_recurrence (s : Position) (hs : pileCount s ≤ 12) :
    marked s = true ↔ ∀ t, Move s t → marked t ≠ true := by
  rcases s with ⟨a,b,c,d,e,f⟩
  simp only [pileCount] at hs
  have h := certificate_checked ⟨a, by omega⟩ ⟨b, by dsimp; omega⟩
    ⟨c, by dsimp; omega⟩ ⟨d, by dsimp; omega⟩
    ⟨e, by dsimp; omega⟩ ⟨f, by dsimp; omega⟩
  simp only [check, beq_iff_eq] at h
  rw [h]
  simp only [List.all_eq_true, Bool.not_eq_true', mem_successors, Bool.eq_false_iff]

/-- The certificate agrees with the recursive game semantics everywhere in S. -/
theorem losing_iff_certificate (s : Position) (hs : pileCount s ≤ 12) :
    Losing s ↔ marked s = true := by
  induction s using (measure tokens).wf.induction with
  | h s ih =>
    rw [losing_iff, certificate_recurrence s hs]
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro hm
    exact not_congr (ih t (move_decreases hm) (le_trans (move_pileCount_le hm) hs))

/-- Six piles of size five and six of size six. -/
def target : Position := ⟨0,0,0,0,6,6⟩

/-- The twelve-pile target is a previous-player win: the player to move loses. -/
theorem target_losing : Losing target := by
  apply (losing_iff_certificate target (by decide)).mpr
  decide +kernel

/-- Every present pile exceeds the integer ceiling of one third of the pile count,
and the number of odd piles is even. -/
def Criterion (s : Position) : Prop :=
  let k := pileCount s
  let threshold := (k+2)/3
  (s.1 > 0 → 1 > threshold) ∧
  (s.2.1 > 0 → 2 > threshold) ∧
  (s.2.2.1 > 0 → 3 > threshold) ∧
  (s.2.2.2.1 > 0 → 4 > threshold) ∧
  (s.2.2.2.2.1 > 0 → 5 > threshold) ∧
  (s.2.2.2.2.2 > 0 → 6 > threshold) ∧
  (s.1 + s.2.2.1 + s.2.2.2.2.1) % 2 = 0

/-- The target meets the stated threshold and parity criterion. -/
theorem target_criterion : Criterion target := by unfold Criterion; decide

/-- Explicit prediction under refutation; nonempty positions satisfying Criterion
are predicted to be next-player wins. This is a hypothesis, not a quotation. -/
def PredictedClassification : Prop :=
  ∀ s : Position, pileCount s > 0 → Criterion s → ¬ Losing s

/-- The explicit next-player classification is contradicted by the target. -/
theorem predicted_classification_refuted : ¬ PredictedClassification := by
  intro h
  exact h target (by decide) target_criterion target_losing

#print axioms target_losing
#print axioms predicted_classification_refuted

end D5.S0.Certificates.Games.VersionBTwelvePileRefutation
