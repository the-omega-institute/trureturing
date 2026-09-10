/- GID: D5/S0/Certificates/Games/VersionBOddCountUnderdetermines
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/VersionBOddCountUnderdetermines
   mirror-E: none(waiver:kernel-checked-finite-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.OddCountDetermines; result=D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.odd_count_does_not_determine; claim=D5/S0/Certificates/Games/VersionBOddCountUnderdetermines.OddCountDetermines
   digest: Two in-scope twelve-pile positions have six odd piles and opposite normal-play Version B outcomes, so pile count and odd-pile count do not determine losing status. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Odd-pile count underdetermines Version B

Positions record multiplicities of sizes one through seven, with no bound on
pile count. Single removal and simultaneous removal strictly decrease tokens.

We recheck the compact bit certificate from VersionBTwelvePileRefutation in
this wider game's own semantics. Its domain is the closed set of positions
with at most twelve piles and no size-seven pile. The dense six-coordinate
stars-and-bars rank uses 18564 bits; no rank-injectivity assertion is needed.
Kernel reduction verifies every local recurrence, and token induction proves
agreement with Losing. This is a new certificate check for the wider Move,
not a transport of the narrow Losing theorem.

Six fives and six sixes are losing. Six sixes and six sevens have an all-move
to that position and are not losing. Both have twelve piles, six odd piles,
and all sizes strictly above four. The two witnesses refute the closed
proposition OddCountDetermines, without specifying any allowed-count set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Games.VersionBOddCountUnderdetermines

/-- Multiplicities of pile sizes 1, 2, 3, 4, 5, 6 and 7, respectively. -/
abbrev Position := Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- Number of nonempty piles. -/
def pileCount : Position → Nat
  | ⟨a, b, c, d, e, f, g⟩ => a + b + c + d + e + f + g

/-- Total number of tokens, the well-founded measure. -/
def tokens : Position → Nat
  | ⟨a, b, c, d, e, f, g⟩ => a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g

/-- Successors obtained by removing one token from exactly one nonempty pile. -/
def singleSuccessors : Position → List Position
  | ⟨a, b, c, d, e, f, g⟩ =>
    (if a = 0 then [] else [⟨a-1,b,c,d,e,f,g⟩]) ++
    (if b = 0 then [] else [⟨a+1,b-1,c,d,e,f,g⟩]) ++
    (if c = 0 then [] else [⟨a,b+1,c-1,d,e,f,g⟩]) ++
    (if d = 0 then [] else [⟨a,b,c+1,d-1,e,f,g⟩]) ++
    (if e = 0 then [] else [⟨a,b,c,d+1,e-1,f,g⟩]) ++
    (if f = 0 then [] else [⟨a,b,c,d,e+1,f-1,g⟩]) ++
    (if g = 0 then [] else [⟨a,b,c,d,e,f+1,g-1⟩])

/-- Removing one token from every nonempty pile; size-one piles disappear. -/
def allSuccessor : Position → Position
  | ⟨_, b, c, d, e, f, g⟩ => ⟨b,c,d,e,f,g,0⟩

/-- The first legal move relation. -/
def SingleMove (s t : Position) : Prop := t ∈ singleSuccessors s

/-- The simultaneous move is legal only in a nonempty position. -/
def AllMove (s t : Position) : Prop := pileCount s ≠ 0 ∧ t = allSuccessor s

/-- Either kind of legal move. -/
def Move (s t : Position) : Prop := SingleMove s t ∨ AllMove s t

private theorem single_properties {s t : Position} (h : SingleMove s t) :
    tokens t < tokens s ∧ pileCount t ≤ pileCount s ∧
      t.2.2.2.2.2.2 ≤ s.2.2.2.2.2.2 := by
  rcases s with ⟨a,b,c,d,e,f,g⟩
  simp only [SingleMove, singleSuccessors, List.mem_append, List.mem_ite_nil_left,
    List.mem_singleton, or_assoc] at h
  rcases h with h | h | h | h | h | h | h <;>
    rcases h with ⟨h, rfl⟩ <;> simp only [tokens, pileCount] <;> omega

/-- Every move strictly reduces the token count. -/
private theorem move_decreases {s t : Position} (h : Move s t) : tokens t < tokens s := by
  rcases h with h | ⟨hne, rfl⟩
  · exact (single_properties h).1
  · rcases s with ⟨a,b,c,d,e,f,g⟩
    simp only [pileCount] at hne
    simp only [tokens, allSuccessor]
    omega

private theorem move_pileCount_le {s t : Position} (h : Move s t) :
    pileCount t ≤ pileCount s := by
  rcases h with h | ⟨_, rfl⟩
  · exact (single_properties h).2.1
  · rcases s with ⟨a,b,c,d,e,f,g⟩
    simp only [pileCount, allSuccessor]
    omega

/-- Previous-player win in normal play: every legal successor is not losing.
This well-founded recursion includes the empty position as a loss. -/
def Losing (s : Position) : Prop := ∀ t, Move s t → ¬ Losing t
termination_by tokens s
decreasing_by exact move_decreases ‹Move s t›

/-- The recursive normal-play characterization. -/
private theorem losing_iff (s : Position) : Losing s ↔ ∀ t, Move s t → ¬ Losing t := by
  rw [Losing]

private theorem move_no_sevens {s t : Position} (hm : Move s t)
    (hs : s.2.2.2.2.2.2 = 0) : t.2.2.2.2.2.2 = 0 := by
  rcases hm with h | ⟨_, rfl⟩
  · have := (single_properties h).2.2
    omega
  · rcases s with ⟨a,b,c,d,e,f,g⟩
    rfl

private def successors (s : Position) : List Position :=
  singleSuccessors s ++ if pileCount s = 0 then [] else [allSuccessor s]

private theorem mem_successors (s t : Position) : t ∈ successors s ↔ Move s t := by
  simp [successors, Move, SingleMove, AllMove]

-- Multiplicative binomial calculation, avoiding Pascal-tree reduction.
private def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | n, k+1 => n * binomial (n-1) k / (k+1)

private def rank : Position → Nat
  | ⟨a,b,c,d,e,f,_⟩ => a + binomial (a+b+1) 2 + binomial (a+b+c+2) 3 +
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
      check ⟨a.val,b.val,c.val,d.val,e.val,f.val,0⟩ = true := by
  decide +kernel

private theorem certificate_recurrence (s : Position) (hs : pileCount s ≤ 12)
    (hz : s.2.2.2.2.2.2 = 0) :
    marked s = true ↔ ∀ t, Move s t → marked t ≠ true := by
  rcases s with ⟨a,b,c,d,e,f,g⟩
  change g = 0 at hz
  subst g
  simp only [pileCount] at hs
  have h := certificate_checked ⟨a, by omega⟩ ⟨b, by dsimp; omega⟩
    ⟨c, by dsimp; omega⟩ ⟨d, by dsimp; omega⟩
    ⟨e, by dsimp; omega⟩ ⟨f, by dsimp; omega⟩
  simp only [check, beq_iff_eq] at h
  rw [h]
  simp only [List.all_eq_true, Bool.not_eq_true', mem_successors, Bool.eq_false_iff]

private theorem losing_iff_certificate (s : Position) (hs : pileCount s ≤ 12)
    (hz : s.2.2.2.2.2.2 = 0) :
    Losing s ↔ marked s = true := by
  induction s using (measure tokens).wf.induction with
  | h s ih =>
    rw [losing_iff, certificate_recurrence s hs hz]
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro hm
    exact not_congr (ih t (move_decreases hm) (le_trans (move_pileCount_le hm) hs)
      (move_no_sevens hm hz))

/-- Number of piles with odd size. -/
def oddPiles : Position → Nat
  | ⟨a,_,c,_,e,_,g⟩ => a + c + e + g

/-- Every present pile strictly exceeds the ceiling of one third of pile count. -/
def EveryPileExceedsThreshold (s : Position) : Prop :=
  let threshold := (pileCount s + 2) / 3
  (s.1 > 0 → 1 > threshold) ∧
  (s.2.1 > 0 → 2 > threshold) ∧
  (s.2.2.1 > 0 → 3 > threshold) ∧
  (s.2.2.2.1 > 0 → 4 > threshold) ∧
  (s.2.2.2.2.1 > 0 → 5 > threshold) ∧
  (s.2.2.2.2.2.1 > 0 → 6 > threshold) ∧
  (s.2.2.2.2.2.2 > 0 → 7 > threshold)

/-- Losing status agrees for all in-scope pairs with equal pile and odd-pile counts. -/
def OddCountDetermines : Prop :=
  ∀ s t : Position, 3 ≤ pileCount s → 3 ≤ pileCount t →
    EveryPileExceedsThreshold s → EveryPileExceedsThreshold t →
    pileCount s = pileCount t → oddPiles s = oddPiles t →
    (Losing s ↔ Losing t)

/-- Six piles of size five and six of size six. -/
def sixFives_sixSixes : Position := ⟨0,0,0,0,6,6,0⟩

/-- Six piles of size six and six of size seven. -/
def sixSixes_sixSevens : Position := ⟨0,0,0,0,0,6,6⟩

/-- The first witness is in scope at twelve piles, has six odd piles, and loses. -/
theorem sixFives_sixSixes_witness :
    pileCount sixFives_sixSixes = 12 ∧ 3 ≤ pileCount sixFives_sixSixes ∧
    EveryPileExceedsThreshold sixFives_sixSixes ∧ oddPiles sixFives_sixSixes = 6 ∧
    Losing sixFives_sixSixes := by
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · unfold EveryPileExceedsThreshold
    decide
  · apply (losing_iff_certificate sixFives_sixSixes (by decide) (by decide)).mpr
    decide +kernel

/-- Simultaneous removal from six sixes and six sevens reaches six fives and six sixes. -/
theorem sixSixes_sixSevens_all_move :
    AllMove sixSixes_sixSevens sixFives_sixSixes := by
  constructor <;> decide

/-- The second witness is in scope at twelve piles, has six odd piles, and does not lose. -/
theorem sixSixes_sixSevens_witness :
    pileCount sixSixes_sixSevens = 12 ∧ 3 ≤ pileCount sixSixes_sixSevens ∧
    EveryPileExceedsThreshold sixSixes_sixSevens ∧ oddPiles sixSixes_sixSevens = 6 ∧
    ¬ Losing sixSixes_sixSevens := by
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · unfold EveryPileExceedsThreshold
    decide
  · intro h
    exact (losing_iff sixSixes_sixSevens).mp h sixFives_sixSixes
      (Or.inr sixSixes_sixSevens_all_move) sixFives_sixSixes_witness.2.2.2.2

/-- Pile count and odd-pile count do not determine losing status on the stated scope. -/
theorem odd_count_does_not_determine : ¬ OddCountDetermines := by
  intro h
  obtain ⟨hs12, hsk, hst, hso, hsl⟩ := sixFives_sixSixes_witness
  obtain ⟨ht12, htk, htt, hto, htl⟩ := sixSixes_sixSevens_witness
  exact htl ((h sixFives_sixSixes sixSixes_sixSevens hsk htk hst htt
    (hs12.trans ht12.symm) (hso.trans hto.symm)).mp hsl)

#print axioms Position
#print axioms pileCount
#print axioms tokens
#print axioms singleSuccessors
#print axioms allSuccessor
#print axioms SingleMove
#print axioms AllMove
#print axioms Move
#print axioms Losing
#print axioms oddPiles
#print axioms EveryPileExceedsThreshold
#print axioms OddCountDetermines
#print axioms sixFives_sixSixes
#print axioms sixSixes_sixSevens
#print axioms sixFives_sixSixes_witness
#print axioms sixSixes_sixSevens_all_move
#print axioms sixSixes_sixSevens_witness
#print axioms odd_count_does_not_determine

end D5.S0.Certificates.Games.VersionBOddCountUnderdetermines
