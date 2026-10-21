# Native refinement of acquired first-bootstrap retention

## 1. Source instance, domains and finite descriptions

**Convention 1.1 (owning construction).** Write
[GENERAL](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md)
for the general-target construction, and retain its names ARC, RCA, GCA,
CYCLE, UAS, CAP, CSA and OPEN_ROW. The fixed supplier bodies are those at
`b12b6db066805e73725c5193e747a23a3bd4146d`; GENERAL's published §§1–20
and its separately stated historical bindings keep their own scopes.
This volume supplies the native refinements used by GENERAL §§21–22.
Its assertions concern the named changed apparatus $G_B$, not an upgrade
of the old running apparatus.

Keep exactly GENERAL Definition 11.1's finite $L,w_0,w_1,e,p,c_j$.
The first-store slots $c_0,\ldots,c_{e-1}$ and their order are fixed;
$w_0[p]=0,w_1[p]=1$. Exchanging the two empty-effect row records changes
their serialization but not their state-keyed map, initial fields or
entry. No reassembly of $L$ is used to redefine this pair.

Use GENERAL Definition 21.5's complete unlabelled domains
$\mathcal R_B,\mathcal C_B,\mathcal A_B$: actual histories from one
entrance; all acquired prefixes of both first loads, matching later
capture/load, both modes, all seven source languages and length-delimited
history inputs including incomplete frames and complete typed rejections;
and all accepted legacy/general cuts of authentic completed predecessors.
Common prefixes are single histories. The pointwise finite-supply and
original-local-termination assumptions apply to promised returns only.
They supply no future completion to an earlier finite cut.

**Definition 1.2 (finite row convention).** Use PR57.03's opcode numbers
$0,\ldots,9$ in the order RD, WR, ML, MR, EX, BF, IN, OUT, TOK, CTL.
A row with number $q$ is

$$
U(q)U(o)U(i)U(j)U(s)U(q_0)U(q_1),\qquad U(n)=1^n0,
$$

followed, in the archival row item, by its framed finite-effect list.
Unused fields are zero. A non-testing row has equal successors. RD tests
its newly read symbol; testing CTL tests its designated public latch.
The fixed bootstrap end/cursor variants have RCA Definition 14.1's
finite-store guard. They do not read an ordinary-tape address or a seal.
Finite effects have ARC Definition 6.2's constructor order: preserve;
literal/latched finite-bit assignment; current/predecessor marker update;
fixed stage/version selection; fixed cursor advance; halt; F receipt.
Each slot, latch, port, symbol, stage and effect tag is a finite literal.
No effect has a runtime word, address or counter as argument.

Let $\operatorname{row}(o,i,j,s,q_0,q_1;f)$ denote this exact encoding,
with its state field supplied by the named row. Encode $f$ as the RCA
list of tagged constructors and their unary finite-location fields.
Its tags are not further opcodes. The installer removes archival list
framing in RCA Definition 12.2's order. Check guards before execution;
on success perform the core, ordered finite effects, designated test
and successor, then the common receipt. RD tests its just-copied symbol;
CTL tests the designated latch after its indicated finite effects.

The finite variant annotation is also encoded, as in RCA12.2: its
ordered cases are ordinary, literal-symbol WR, latched-bit WR, public
IN, private IN, boundary EX, fresh-control WR, bootstrap NEXT,
bootstrap ADVANCE and bootstrap DONE. Within the framed finite-effect
description use the unary index of that case, followed by its finite
literal location/stage fields and the framed effect list. The active
version and named row fix every such field in
§2's table; literal versus latched WR therefore remains distinct even
when their seven PR57 fields coincide. This is an encoding of existing
finite local variants. Its nonzero tag never denotes a new core opcode.

## 2. The active first loader and its ordinary authority

**Definition 2.1 (paid active store and entry).** The extended original
boot installs the following fixed table $H_B$ before entering its first
NEXT. Its row bits are paid initial control bits, separate from the
absent target slots $c_j$. The original irreducible primitive bootstrap
installs this finite table bitwise, just as it installs the earlier
original control. This is part of the explicitly changed initial boot;
no row of $L$ or $G_B$ installs $H_B$. Its constants depend on fixed $L$
and $e$, not on $G_B$'s description or length. Its physical control store,
PC and cursor are disjoint from the target first store and from tape74.

The same original extended boot constructs L74 and R74 by two boundary
variants, installs their head at R74, owner74=$A$, the current read slot
$R_{74}=1$, and the phase-limited write slot $W_{74}=1$. It installs
Mirror=1, Retained=0 and sealed=0. The first-version installation-owner
and constructor authority and its cursor at $c_0$ are the ordinary
fresh-version ones of RCA14.1. These finite bits and the actual first
cursor fields are installed one bit per paid constructor; none is supplied
by a printed permission. L74/R74 enclose no data at this entry.

The unique normalized activation CTL enters $H_B$'s NEXT, disables the
source dispatcher for initialization and fixes this first version. The
only new external inputs in $H_B$ are its IN6 occurrences. Use $\ell=6$;
no local symbol test in this loader overwrites it. When this table is
active, raw target bits are data and cannot supply executable rows.
Second-bootstrap entry is a distinct fixed stage: it uses the original
five-state loader for $E(G_B)$ and never re-enters $H_B$.

**Definition 2.2 (complete first-loader table).** For each fixed
$0\le j<e$ name rows $N_j,I_j,X_j,W_j,M_j,C_j,A_j$ in that order.
After these name $N_e,X_e,W_e,S_e,M_e,D_e$. Assign consecutive state
numbers in this displayed order within $H_B$. This finite unrolling
uses no runtime natural as a PC. Let $N_{j+1}$ mean the next such row,
with $N_e$ the end case. Every effect list not displayed is empty.
All rows have an ordinary receipt.

| Row | Opcode fields $(o,i,j,s)$ | Successor and extra finite effect |
| --- | --- | --- |
| $N_j$, $j<e$ | $(9,0,0,0)$, NEXT variant | $I_j$; select the existing cursor position $c_j$. |
| $I_j$ | $(6,0,6,0)$, public boot IN | $X_j$. |
| $X_j$ | $(4,74,0,0)$, ordinary EX | $W_j$. |
| $W_j$ | $(1,74,6,0)$, latched-bit WR | $M_j$. |
| $M_j$ | $(3,74,0,0)$ | $C_j$. |
| $C_j$ | $(1,0,6,0)$, fresh first-control WR variant | $A_j$; construct exactly slot $c_j$ from latch6. |
| $A_j$ | $(9,0,0,0)$, ADVANCE variant | $N_{j+1}$; advance this fixed cursor by one. |
| $N_e$ | $(9,0,0,0)$, end NEXT variant | $X_e$. |
| $X_e$ | $(4,74,0,0)$, ordinary EX | $W_e$. |
| $W_e$ | $(1,74,0,\ulcorner\mathsf F\urcorner)$, literal WR | $S_e$. |
| $S_e$ | $(9,0,0,0)$ | $M_e$; seal current74 marker, set sealed=1. |
| $M_e$ | $(3,74,0,0)$ | $D_e$. |
| $D_e$ | $(9,0,0,0)$, first DONE variant | Activate the completely written actual first store at its installed entry; set Mirror=0, Retained=1, $W_{74}=0$. |

The row name supplies the state field of Definition 1.2; each displayed
single successor fills both successor fields. $D_e$ uses the fixed
version-entry effect with the completed first store's actual initial
PC, which is $L$'s on either admitted word. It uses no address computed
from an uninstalled main word. Its ordered effects retain
sealed=1, owner74=$A$ and $R_{74}=1$. The later first-store deactivation
preserves these fields; the main graph does not initialize them back to
Mirror or erase them. A first/second-version flag selects these two
distinct DONE cases, so second DONE cannot regrant $W_{74}$.

The guards are also part of this table. Every row requires active $H_B$,
its indicated PC, Mirror=1 and the actual first installation owner.
$N_j,I_j,C_j,A_j$ require cursor $j$ and the fixed version's constructor
authority. $N_j$ has the non-end guard, $N_e$ the end guard. $C_j$ also
requires $c_j$ absent and a binary latch6. There is no guard comparing
that bit with $w_0[j]$. $X_j,X_e$ require $W_{74}=1$ and marked R74;
$W_j,W_e,S_e$ require the current writable unsealed old R cell just
allocated by that EX and $W_{74}=1$. $M_j,M_e$ require the existing
right neighbor and that current owner/right. $D_e$ requires cursor=end,
complete first store and sealed=1. These are finite phase, cursor,
freshness and ordinary primitive guards, with a fixed local footprint.
None tests an unbounded prefix or physically reads a seal track.
The seal flag is an enabling invariant, not an imported symbol.

NEXT's selected position is already the fixed current slot; ADVANCE is
the only cursor-changing row. Thus selecting $c_j$ is preservation of
that finite cursor, not a random-access construction. $C_j$, denoted
WRITE$_L$ in GENERAL21.2, is exactly the fresh finite-bit constructor.
It is distinct from the ordinary latched write $W_j$ on an existing
cell. Every other tape/head/latch/slot remains unchanged except for the
common PC/receipt effects. No bank assignment runs in $H_B$.

**Lemma 2.3 (guards and every partial cut).** On either admitted first
load all the rows of Definition 2.2 execute, and after $j$ complete
iterations the raw target prefix and ordinary74 prefix are exactly the
first $j$ actually consumed bits. Only $D_e$ activates $L$. A cut at
any intermediate row retains exactly its actual partial data and active
$H_B$. In particular the matching74 WR of an IN at preordinal $v$ has
postordinal $v+3$.

Proof. At $N_0$ the paid entry gives cursor0, an absent first store and
empty74 at R. Assume the assertion at $N_j$. NEXT preserves cursor and
tests its non-end finite case. IN changes only latch6, PC and receipt.
EX turns the marked R into blank and creates its new unmarked R. WR
sets that old cell's three symbol bits from the same latch6. MR moves
the head onto its new R. All three operations preserve latch6 and the
first cursor. The ordinary writer right is still1, so each guard is
met. The constructor $C_j$ sees the still-absent $c_j$, the actual bit
and its owner/constructor right. It constructs that bit; ADVANCE selects
the next fixed cursor and no earlier bit is touched. This proves the
induction and every interior state between its steps.

At cursor=end the last NEXT enables EX/WR(F)/seal/MR. The seal effect
acts while the head is at that actual F; the following MR preserves it.
DONE sees complete raw data and the finite flag set by that row,
withdraws writing and enables the actual decoded $L$. Both supplied
words have the same valid keyed map and entry by GENERAL11.2's record
argument, so this next phase is the fixed $L$ in either case. Before
DONE no raw bit changes active $H_B$, including at the IN, EX, ordinary
WR and fresh-control WR cuts. The matching WR is the third executed
row beginning with IN, proving $v+3$. No claim uses a future seal at an
earlier cut. ∎

**Lemma 2.4 (retained seal without a seal observation).** On either
admitted initialization, from first DONE onward tape74 is $w\mathsf F$, with the final F seal track set,
owner $A$, $R_{74}=1$, $W_{74}=0$, and head initially R. These facts
persist through capture, second load, import, services and original00.

Proof. Lemma 2.3 gives the exact symbols, mark and final seal. Enumerate
the fixed writers: $H_B$ has the only74 EX/WR/marker rows and it has
no re-entry; $L$ uses66–69; the second bootstrap writes its own fresh
version; bank rebuilding uses64–68; the new importer only RD/ML/MR74;
other source, channel, original client/verifier/consumer rows have no74
write/effect operand. Their finite token lists have no assignment to
$R_{74},W_{74}$ or owner74. Step applied to a represented74 list changes
bank bytes, never the current physical74. Induction on these actual rows
preserves all asserted tracks and rights. The importer therefore has a
sealed immutable source under current read authority. RD reads only its
three symbol bits; no additional seal test or imported seal bit follows
from, or is needed for, this invariant. ∎

## 3. Closed symbol acquisition on tape74

**Definition 3.1 (source74 importer).** Start after the complete empty
$r_B$-field bank, under Retained and $R_{74}=1$. Give distance $d$,
reverse accumulator $z$, forward symbol word $s$, restore cursor $u$,
parser cursor and output $b$ distinct bank registers. Their assignments
use ARC2.1's full $r_B$-field compiler, whose physical footprint is64–68.
The following is a static finite word/native graph, not an application
of ARC3.2 with $i=74$.

| Entry | Native or expanded word work and successor |
| --- | --- |
| Start | $d:=\varepsilon$; Save. |
| Save | RD(74,4) testing L; true to ScanStart, false to ML74; $d:=1d$; Save. |
| ScanStart | MR74; $z:=\varepsilon$; Scan. |
| Scan | RD(74,4) testing R; true to Reverse, false to Symbol. |
| Symbol | CTL equality cases on unchanged latch4 in ARC's eight-symbol order; select a literal triple $b_0b_1b_2$; then $z:=b_0z$; $z:=b_1z$; $z:=b_2z$; MR74; Scan. |
| Reverse | $s:=\operatorname{Reverse}(z)$; $u:=d$; Home. |
| Home | RD(74,4) testing L; false ML74 and Home; true Restore. |
| Restore | Expanded empty test on $u$; if nonempty MR74; $u:=\operatorname{tail}(u)$; Restore; otherwise Parse. |

Scan's non-R symbol branch tests the seven remaining symbols in that
order, with the last case literal F after excluding the others. Each
test is one encoded public CTL equality row with its two static
successors; the R test itself is the Scan RD. No assignment intervenes
before the symbol is selected. The triple uses ARC/CYCLE's actual code
order $L,R,0,1,\square,\mathsf{sep},\mathsf{seal},\mathsf F$.
Thus repeated cons followed by bit Reverse gives the forward triple
concatenation, rather than reversing each code. Source boundary tests
are ordinary symbol reads, not head/marker-track observations.

Parse copies $s$ to a cursor and clears $b$. Read triples by three
bounded Takes. For each of $e$ unrolled positions require a complete
0/1 symbol triple and cons that literal bit to a reverse bit accumulator.
Require the next complete triple to be F and then exact exhaustion.
Reverse the bits to bootWitness. Compare it by Equal to $w_0$ and $w_1$
and require the disjunction, retaining the imported value. A short
triple, missing/extra symbol, nonbinary payload, wrong delimiter or failed
membership takes the finite InitializationFault CTL after restoration.
This specifies every parser case on finite copied input, without adding
a whole-word native leaf. $e$ is a fixed syntax constant; a unary-counted
implementation of these same fixed cases is not required.

**Theorem 3.2 (closed import, rights and restored head).** On either
admitted load this graph terminates with bootWitness equal to the actual
first input word, unchanged symbols and seal on74, its original entry
head restored, and its current read/owner slots preserved. Its parser
never observes the seal track. It also terminates, with the stated finite
parse failure where applicable, on any finite unchanged ordinary source
with these boundaries/rights and this disjoint compiler footprint.

Proof. Let $h$ be the entry head's finite distance from L and $m$ the
number of ordinary cells between L and R. After $a$ Save iterations the
head distance is $h-a$ and $d=1^a$. Assignments preserve head74 and its
source symbols, since they touch only64–68. At $a=h$ Save reads L and
ScanStart enters the first ordinary position, including R if $m=0$.

After $t$ Scan iterations its head is at ordinary position $t$, or R
when $t=m$. Its accumulator is the reverse of the first $t$ symbol
triples. Each symbol branch fixes the three literals before rebuilding
the bank, so the proof does not assume survival of latch4 across a
cons. MR74 moves to the next existing cell. The unchanged finite R is
therefore reached in exactly $m$ such iterations. Reverse yields the
actual ordinary symbol word in forward order. Home decreases its
current distance to L. Restore has initially $h$ marks and preserves
distance $h-|u|$ at its testing entry; hence its $h$ MRs return to the
original cell, even when that cell was R. Both symbol word and saved
distance survive unchanged bank fields. All source moves/reads have
the actual $A$ read right; no writer is run and no encoded reference
creates authority.

The parser consumes one complete triple per required symbol and
requires exact end. A partial triple or missing field fails finitely;
zero length and all eight finite symbol alternatives are covered.
On the admitted source $m=e+1$ and the word is precisely $w\mathsf F$
by Lemma 2.4, so all cases and the disjunction succeed with $b=w$.
The proof of the physical seal is Lemma 2.4, independent of $s$; an
ordinary seal symbol would be a different symbol and fail the grammar.
The parser does not pretend the seal track was copied in $s$. ∎

**Proposition 3.3 (exact correspondence to ARC's importer).** ARC3.1's
quantifier remains $i\in\{26,28,29\}$. Its Save/Scan/Reverse/Home proof
has exactly the following correspondence to Theorem 3.2: fixed source
$i$ becomes74; its ordinary symbol length becomes $e+1$; its saved
head distance becomes this $h$; its read token becomes the actual
$R_{74}$; and its untouched-source condition is Lemma 2.4. Compiler
ports64–68, symbol triples, distance register and restoration invariant
are the same. ARC3.2 itself is not broadened.

Proof. Each source operation in the table in Definition 3.1 names74
literally. Every intervening assignment has the same disjoint footprint
and copies all unchanged fields. The four decreasing quantities in the
preceding proof are the finite Save distance, remaining Scan cells,
Reverse cursor and restore counter, with no dependency on the numerical
name of that disjoint source. All branch and delimiter cases were proved
there for74. The added parser fixes its binary/F grammar instead of
using ARC's CAP-descriptor grammar. Thus it supplies the missing instance
and its parser join, rather than deriving one from ownership alone. ∎

## 4. Literal 75-port semantics and supplier correspondence

**Definition 4.1 (complete new raw codec and Step75).** A physical word
encodes exactly75 port lists in order0–74, each cell with eight literal
tracks, followed by the ordered finite-slot vector, active/raw versions,
PC, latches, heads/cursor/token fields and fixed source binding in the
RCA/ARC physical tuple grammar. Duplicate representations of a shared
physical finite bit use one catalog identity. The finite catalog is the
union of the actual earlier boot, paid $H_B$, first raw store, $L$,
second raw store, $G_B$ and their fields, in GENERAL2.5's order.
Absent,0,1 remain separate values; partial target bits remain separate
from the last completed active table. Tally, represented event lists,
input cursors and completed annotations are simulator words, not extra
old physical coordinates.

Earlier versions keep their own literal $E$ and archival codecs. Decode
each by that fixed version's codec and translate its finite variant tags
to Definition 1.2's cases by the owning row's local meaning. This finite
catalog translation preserves every operand/effect and never rewrites
raw first-store bits. In particular it leaves $w_0,w_1,c_p$ unchanged.
Shared owner/read/phase fields are catalog identities preserved by
second-version installation; only that version's absent local fields
are fresh constructors. Its initial-control word does not reconstruct
or regrant the already present74 rights.

Step75 is the following finite word program. Parse and exhaust this
tuple, requiring75 lists, eight tracks per cell and the declared finite
ranges. Find the active row: before first DONE select Definition 2.2's
fixed table; in capture select the actual decoded first store; during
second boot select its fixed five-state table; after second DONE select
the actual decoded second store. Lookup traverses its complete framed
list by unique state key. Validate ports0–74, latches0–7, symbols0–7,
Boolean tables0–255, successor/entry indices, variant/effect tags and
finite-slot bounds; absent, duplicate or malformed main rows have no
enabled successor. Preserve their actual already executed history.
There is no canonical replacement on a raw DONE.

Copy the prestate; locate marked cells by Nth and a full finite mark
scan; preserve old-value operands while applying core and ordered
effects. Finite port cases have75 branches, with74 last. Replace and
AppendItem have ARC2.1's expansions. The transformations are:

| Core/variant | Complete represented change before receipt |
| --- | --- |
| RD | With its read right select the actual marked symbol's three bits into its latch and take its literal equality successor. |
| Ordinary WR | Require the actual writer, writable marked cell and literal/latched variant; replace its three symbol bits only. |
| ML/MR | Check owner/right and existing neighbor/boundary; clear old and set adjacent head mark. |
| Ordinary EX | Require writer and marked R; retain old R identity/head as blank and append one unmarked R. |
| BF | Apply its eight-bit truth table to the actual operand subfields, changing only result subfield3. |
| IN | Use the actual version/PC/site kind; consume its next actual bit and change only the designated latch. |
| OUT | Record the actual permitted output bit, with no live OUT from a represented bit. |
| TOK | Require named source=1,destination=0 and perform their two finite updates. |
| CTL | Perform its literal ordered finite effects and its actual test/successor, with the fixed cursor/end variants of §2 when selected. |
| Boundary/fresh-control WR | Construct its one named boundary cell or one absent finite location, with its literal/latched value and specified cursor effect. |

Append the common receipt at the actual meter append R, retaining that
cell's identity, creating one new R and moving the append mark. Preserve
the core's newly updated meter read mark, including coincident head roles.
Append the exact event, one tally mark and any actual acquisition/completed
annotation. Fold RCA12.4's request/commit/pending interpretation on these
events separately. Guard failure returns simulated-illegal, not a source
refusal. Each Step executes one represented row, with no semantic Call.

**Lemma 4.2 (raw Step square and finite domain).** Let $X$ be any reached
raw state of the changed75-port apparatus, $\operatorname{enc}_B(X)$
its complete physical encoding, and $u$ its actual supplied bit at an IN.
Then Step75 is enabled on this encoding exactly when the prescribed
native row is enabled, and

$$
\operatorname{phys}(\operatorname{Step75}(\operatorname{enc}_B(X),u))
=\operatorname{enc}_B(\operatorname{native}_B(X,u)).
$$

Its event, label and receipt are identical as well. At a failed native
guard it returns simulated-illegal with no represented executed event.
This includes raw wrong supply, partial first load, all importer and
compiler interiors, channel phases and the final halt edge; a positive
recovery assertion outside $\mathcal C_B$ is not inferred.

Proof. For RD/WR the same port-list item and marked cell are selected;
the guard and symbol fields in the table give the identical local value.
Moves change the same adjacent marks; EX changes the same old R and
appends the same new R. BF has a finite truth table; IN/OUT select the
same actual site/latch bit. TOK uses the same named finite slots.
Each CTL constructor sets the very slot or existing marker named by its
actual row, in order, and hence preserves dependencies between effects.
Fresh WR constructs the same absent first/second-version bit, never an
ordinary74 cell. Definition 2.2 supplies the exact pre-DONE table, so no
case borrows a not-yet-enabled row. The end/first DONE effects are its
finite cursor and version cases. All unmentioned data are copied.
Combining coincident identities before the common receipt preserves the
core's new read mark and gives exactly one receipt. These local cases
exhaust the grammar, including port74. Undefined decoder or guard cases
fail in both descriptions. Every scan has a finite copied source and
every word helper has its finite compiler expansion; thus one Step is
finite even for a row of an older interpreter. ∎

**Definition 4.3 (relations to the fixed74-port suppliers).** There are
three distinct correspondences; they are not an equality of old/new runs.

| Supplier surface | Relation in the changed instance |
| --- | --- |
| ARC6.2, GCA2.4/4.1, CYCLE5.1 raw codec | Same tuple/row/effect grammars, with the complete port vector length75, range0–74, catalog/active tables of4.1 and site reservoir of GENERAL21.9. |
| ARC2/RCA11 bank compiler | At a word boundary, the exact register valuation is represented by the complete $r_B$-field bank, its actual descriptor/parity; interior cuts use the raw partial-bank relation. Old program fields inject by their hygienic names; every added field is also emitted. |
| GCA/CYCLE code-dependent entries and roles | Symbolic call-path/entry/exit/port/family/role items of the final expanded $G_B$ and earlier fixed graphs, with the actual new PC numbers, finite tags and catalog identities. |

For a literal row whose footprint lies below74, the local relation to
its supplier row identifies those actual operand cells/marks, named
finite slots and latches, and renames its fixed PC/successor labels by
the inlining map. All unmentioned cells,74 and finite slots form its
frame. It also identifies the actual meter prestate; its next receipt
is the receipt from that changed-run prestate. For $H_B$ and the74
importer the row is instead one of the newly defined rows in §§2–3.

This relation is local to one row or to a compiled word instruction.
The whole changed run does not project to an old run with the same
absolute tally: it has extra receipts, different code, larger banks and
longer descriptions. In particular adding fields is not a rowwise
renaming of an old bank-emission trace.

**Proposition 4.4 (the compilation and metadata joins).** These relations
give finite executable replacements for every74-port supplier routine
used in GENERAL21, with the following exact joins.

Proof. A source-level word assignment has a finite list of $r_B$ fields.
RCA11.3's first pass measures precisely those fields from the unchanged
source bank, and its second emits the same fields, including each new
persistent word and temporary, into the other bank. Separators/F/seal,
actual Base, descriptor count/write and parity CTL establish the new
boundary relation. The usual per-field induction is over this actual
finite list, so it proves preservation of unchanged bootWitness/bootRef
and service fields. Its interior relation is the emitted prefix plus
remaining fields of that list, not an assumed complete bank. Scratch
remains64–68; sources26/28/29/69/70/73/74 are disjoint and retain the
head facts their respective proofs require. Old CAP descriptors and
new RCA descriptors keep their different grammars and ordinals.

Use Definition4.1 to replace every raw-state count/range in Step, input
extraction, body layout, Image serializer and Image-value checker,
including each nested older-history interpreter. All are finite source
programs with fixed port alternatives, not source-dependent code patches.
Lemma4.2 proves their common local semantics. A numeric port74 is valid
only in this new codec; it was not valid in the old74-list codec.

After expanding/numbering the resulting graph, construct GCAEntries and
ConstructionDirectory as GENERAL2.2's exact pair. SourceEntrySet contains
each parity alternative of the actual01 dispatch CTL to $F^A$'s header
prelude; SourceExitSet its final idle CTL to InnerReturn. The parser
uses these fixed slots, exhausts their lists, checks unique keys, all75
port bounds, actual CTL effects and the indicated successors. Extend
the construction-role directory with the fixed $H_B$ mirror span,
source74 import, and the two new initial69 field exports/stage; all
other construction sites follow their actual hygienic paths. For the
earlier loader the directory's PCs are the independently fixed $H_B$
PCs. Its version tag distinguishes them from main PCs with equal
numerals. On EX its role fold adds the old R immediately, on seal it
closes only that actual span. The directory is finite archival data,
not a native grant or a source of input bits.

There is no dependence of a graph edge on the digits of its own row
number: graph edges and call paths are symbolic until numbering, and
metadata are then generated without adding graph instructions. The
fixed capture $L$ acquires the actual resulting $\Delta(G_B)$ and the
second load consumes its matching $E(G_B)$. Field zero is validated
against this same grammar/metadata. The parser reads self-description
from captured backing; no self-description constant enters the graph.
Thus register count, raw codecs, entry tests, role fold and code lineage
all join this one expanded instance. ∎

## 5. Acquisition, immutable resolution and completed predecessors

**Theorem 5.1 (the complete initialization).** Under the admitted two-load
and pointwise supply premises, GENERAL21.3 reaches its first actual
Ready, with bootWitness equal to the consumed first word and bootRef
resolving both its actual74 source and immutable initial69 export/stage.
The original client remains parked and all current source/consumer
resources have their specified owners. This conclusion uses no physical
seal-reading operation.

Proof. Lemmas2.3–2.4 give the lawful first load and immutable74 source.
The fixed keyed $L$ then performs its unchanged native capture on66–69;
the matching second five-state loader installs $G_B$. No importer or
bank instruction is required before that code's empty-bank prelude.
Proposition4.4 gives that prelude with all $r_B$ fields. Theorem3.2
supplies the actual first word and head restoration. Old26/28/29 imports
still fall within ARC3.1's original domain with their original tokens,
grammar joins and restored heads. No original workspace is lent to this
compiler and no parked24/25/27 cell is changed.

Complete the old ordered initial69 fields, keeping field zero first.
GENERAL21.3's next field contains the actual imported word and source
record; export first measures its real destination Base and length,
writes its payload/F/seal and its complete68 descriptor. The next
field copies that just-completed descriptor by the positioned dry-count
stage schema; describe that stage once. Its own descriptor is not its
payload and is never recursively staged. All these routines have their
actual disjoint sources and finite counts by Proposition4.4.

Freeze this complete initial prefix before ManifestPrefix, whose two
entry moves skip L69 and its sole sentinel. It imports the actual old
fields and these two fields, not any later staging. Exact arity, word,
source and measured placement comparisons therefore identify this same
export and complete staged descriptor. The74 source record's sealed
value is justified by Lemma2.4; its export seals by the actual export
rows. No parser derives a current right from those printed values.
Retain both complete references and the imported word in the manifest
and bootRef. Initializing the remaining fields copies them unchanged
through every complete-bank rebuild. The actual invocation TOK and
Ready CTL finish the entry. All component scans and supplies are finite.
All later writes preserve these intervals and complete persistent words,
so induction also proves the required immutable-resolution invariant. ∎

**Definition 5.2 (bound service on75 lists).** Boundary starts from the
encoded changed entrance with its actual acquired seed and fixed public
code; first-loader INs use bootWitness from this immutable manifest,
never a branch-selected canonical word. Other typed site kinds use their
actual fixed/acquired reservoirs. Its stop is the conjunction activation
complete, completed-cycle count $|M|$, and the actual outer Ready PC.
Prefix has exactly its constructed $1^k$ countdown. Both use Step75.
The source locator consumes at most the constructed $b$ Steps, comparing
the actual outer version/PC/effect entries from Proposition4.4 and the
completed item index; entry/exit tallies are successor tallies $e,f$.
Literal nested PCs in bank data cannot satisfy that outer test.

Issue uses the actual accepted grammar/arithmetic and copies manifest,
bootWitness, full bootRef, consumed $I_k,k$ and all fixed binding fields
to immutable backing. Call resolves that specific package under its
current invocation slot and runs Prefix on the copied data. The ten-field
body binding contains complete references and target phase, with bootRef
nested in its boot-reference field; it contains no bootWitness payload.
The actual service/package manifests retain that payload separately.

**Lemma 5.3 (authentic predecessor and binding correspondence).** On an
authentic completed predecessor Boundary and Prefix return that run's
actual earlier history, source locator returns the actual unique $e,f$,
and Issue/Call use precisely its acquired $c,p,k$ and first word. The
accepted target names are exactly GENERAL21.5's legacy/general names,
including every $[a_B,b]$ cut and every completed source-call $[e,f]$ cut.

Proof. Simultaneously induct on completed outer cycles and finite return.
Theorem5.1 is the zero-cycle case. A completed source item is CAP's full
original finite call, ACK/source TOK/idle CTL, normalization and closed
acquired28/29 parse, with its actual ordered dependencies and origins.
A history item contains its actual mode and entire retained frame plus
outcome and received bindings, appended only at its final return.
Thus the frozen predecessor supplies the exact reservoirs of every
earlier IN. In particular its first-loader bits are Theorem5.1's
imported bits on both loads. Induction with Lemma4.2 reproduces every
earlier native row and receipt, including older converter instructions.

Boundary's conjunction is false at preactivation and earlier Readies;
at this predecessor it is true. Prefix stops after exactly $k$ finite
Steps. The literal source dispatch and final idle CTL occur once for
that completed source item, before later normalization/CaptureCAP.
Their actual metadata and completed index uniquely select them, giving
$a_B<e<f<b$; the bounded locator reaches them before its budget ends.
Unary cancellation and Cat therefore prove the unchanged ranges and
$k=a_B+t$ or $k=e+t$; legacy mode keeps its own strict-Zero tests.
All origins and absolute tallies are those of this changed run.

Each current reference callback uses the actually positioned receiver73
and acquired immutable backing, with live invocation and copy/read
resources as proved below. Consequently Issue's data are those of the
selected cover, and Call's are those of that specific package. No
latest-object pointer, canonical-word substitution or historical token
grants an entry. The remaining finite channel and decoder work in §6
gives the next completed item, closing the simultaneous induction.
Its dependency decreases in completed predecessors; a represented Step
does not recursively request the semantic result of an older Call. ∎

## 6. Independent bodies and actual installed use

**Theorem 6.1 (all declared partial cuts).** GENERAL21.6–21.8's four
independent bodies recover their own actual $h\in\mathcal C_B$ and full
75-port endpoint. They do not use the service's bootWitness to repair a
body. Their induced transports have the inverse, triangle and native
edge laws on exactly this entire unlabelled domain.

Proof. The75 tape components and finite catalog give the same unary
track/socket inverse as UAS3.2 and CYCLE3.6: fixed outer paths select
every ordered tape, a spine selects each actual eight-track cell, and
absent/left0/right1 select each finite location. Terminal prefix closure
inverts boundary independently, with no full-binary restriction. These
arguments use the newly fixed outer $F_{76}$, not an old74-list parser.

For S/B select the basic families from their own recovered raw record;
for M parse its own basic0–4,6. The actual seed and meter give the true
entrance packet and $n=|h|$. During counted recovery, the already derived
prestate identifies each first-loader IN, its then-current74 R identity
and its matching write ordinal $v+3$. If $v+3\le n$, that body's own
written74 cell supplies the actual bit. Otherwise its own occupied
latch6 record supplies it: no input or overwrite intervenes before WR.
An EX-only blank is not a bit. Before IN neither source is consulted.
This covers every first-loader cut, before/after the differing bit,
before F, before seal and before any later export or manifest.

Other variable sites retain GENERAL4.1's13/70 matching-write cases;
the new importer has RD only. All fixed sites have the stated fixed
code/actual seed supply. Induct on the $n$ row ordinals using Lemma4.2.
Equal prestates give the actual PC, slot, right, head, latch, next input
and complete successor. Earlier simulations themselves execute literal
native rows under this induction. It therefore yields exactly $h$ and
its raw endpoint, without assuming successful historical answers.
S/B compare that entire endpoint; M folds the actual role directory
only after deriving $h$ and compares all seven reselected families.
No future role annotation supplied input to that induction.

T instead starts the paid foundation and supplies only its own optional
bit at each actual IN. The local templates and Step square of §7
compute and compare every one of CYCLE5.3's eleven fields, including
repeated probes, actual bindings, births, aliases and receipt. This
gives the same $h$ and endpoint by record induction. All four procedures
use finite cursors or their decreasing row countdown. Each independent
encoding of the recovered $h$ is its natural support, terminal contour,
occurrence sequence or selected actual memory. Equality of any body
therefore gives equality of histories, and the converse follows from
those independent definitions. Re-encoding another view gives the
inverse/triangle equations. Unique recovered prestates have exactly
the same actual enabled labels/inputs and successors, giving the edge
square whenever both endpoints lie in $\mathcal C_B$. ∎

**Theorem 6.2 (received-body cycle and original consumer).** Every
accepted target at every authentic predecessor completes GENERAL21.9's
eight-publication route under the stated pointwise completion premises.
Its five view publications successively consume only their own received
bodies; final S equality and the separate acquired Image-value check
precede the final ACK, completed item and resource return. Both actual
first loads are covered. The actual original verifier/INITIAL route
after00 remains the one in GENERAL21.12.

Proof. Lemma5.3 supplies the actual target and current immutable binding.
At each publication measure actual71 sender,72 mailbox and73 receiver
bases, initialize their full intervals/F and descriptors, then immediately
stage the three complete placement records on69. Descriptor stage length
comes from its dry count, not the payload length. Stage its own descriptor
once only. Before each copy reload bases and sender length from those
records and Seek both actual endpoints. The six-row tested copy invariant
is bitwise equality of the copied prefix and correct next positions.
Its terminal test, seal and actual TOK handoff establish the next phase.
No helper intervenes in the protected copy/print sequence to invalidate
the three-record recency. Both copies and print therefore use the actual
payload, even at length zero. The current rights/slots are ARC7's
separate physical read, invocation and mailbox resources below74;
Definition4.3's local frame leaves their guards and updates identical.
No claim equates an old token with a new encoded one.

At callback entry obtain the still-current receiver placement and Seek73
before any bank assignment; import to its constructed F. The importer
preserves73 while rebuilding64–68. Check the complete kind, source,
code/bootRef, expected stage/selector/tally and immutable-resolution
fields. Clear candidates first and take sourceBody solely from that
actual import. Current bindings compare the retained actual first word
through immutable manifests; body decoders receive only their separate
body/reference/PublicCode arguments. Theorem6.1 and GENERAL5's past
predicates therefore check the unique selected prefix, demanding no
future F, export, origin or Ready at an earlier target.

Induct through RenderS, FromS, FromB, FromM and FromT and their separate
callbacks. Each return ACKs its own completed channel and returns mailbox
availability before the next publication. No early Ready or completed
item admits another flight. CheckS1 compares two actually received S
bodies and applies the changed75-list Image-value checker to its own
independently recovered value, against the actual acquired target.
FinalReturn alone ACKs this last channel and appends the one five-field
item with its actual ordered received bindings; then invocation TOK and
Ready close Lemma5.3's induction. Each loop has a finite copied word,
actual length, row budget or earlier completed predecessor. Typed history
rejections use their first-detecting finite route and release only held
resources; incomplete inputs make no return promise.

For the original route use the local relation of Definition4.3, not a
projection of the whole history onto an old74-port run. At an actual
source entry fix its full changed-run prefix, including its meter.
Every row of $F^A$ has its original CAP4.6 operands, latch5 inputs,
guards, source/counter effects, row copies and ACK, with the finite
inlining/parity renaming. Its final idle CTL alone has the changed
InnerReturn successor, excluded from the original-task chart. All
added work is outside this original body. On00 the actual twelve
workspace TOKs and final CTL enter the unchanged parked Stop client.
Its output31 is copied through49 to21; SEG-P1 and complete dependencies
travel through50 to verifier32–39. The original finite candidate and
historical-guard enumeration accepts the acquired beta proposal
$(0,B,1)$. The expected binding is separately actually delivered to40,
SEG-R1 travels through51, and consumer40–47 checks its original type,
source, snapshot/count/end and proposal fields before target43 allocation,
copy, seal, OUT, ACK, token return and absorbing halt. Annex work changes
no original semantic event/counter or protected client field. All copied
origins/fences use this actual longer run's coordinates. Thus the original
consumer is preserved, without replacing INITIAL by current-source data
or asserting a global original-$Q$ bridge at added cuts. ∎

**Corollary 6.3 (actual differing recovery).** With the actually supplied
first-Ready AcquisitionOffset request of GENERAL21.11, Call and each
independent body recover $c_p=0$ after $w_0$ and $c_p=1$ after $w_1$.

Proof. Theorem5.1 makes the service reservoir the actual consumed word;
Lemma5.3 runs its literal first-store constructors with those bits.
Theorem6.1 obtains them independently from written74/pending data in
each body. The first Ready target contains the completed fresh slot
$c_p$, so both recover exactly its actual value. The received-cycle
proof consumes this result. Supplying $w_0$ after the actual $w_1$
would give a different raw endpoint and fail the full S/B equality and
M reselection; retaining an unused witness would not prove this corollary.
The request chooses that run's tally, without assuming equal Ready
tallies or internally manufacturing its intended offset. ∎

## 7. Same-run native leaves and structural stencils

**Definition 7.1 (complete recursive bill).** Use GENERAL21.13's vector
recurrence on actual native leaves, refined by first-loader, source74
import, parser, export/stage, service, each decoder/arrow and callback
purpose. A finite test contributes its actual RD/CTL; guard enabledness
does not add an unlisted observation. Every executed row adds one tick,
two fee units and one eight-bit receipt cell. Ordinary EX/boundary
construction adds its one eight-track cell; fresh-control WR adds its
one finite bit. Overwrite, retirement and cleared bank fields subtract
no constructed storage. Sequence and loops use their actual complete
successors. No separately optimized fragment is added.

For the source74 importer the exact leaves are Definition3.1's initial
empty, Save RD/ML/compiled distance cons, initial MR, Scan RD, the selected
finite CTL tests, three full compiled cons assignments and MR, Reverse,
restore copy, Home RD/ML, each expanded empty test/MR/tail, final empty
test, all triple Takes/binary/F/exhaustion tests, Reverse and two Equals.
Parser failure contributes its actual selected branch and CTL. Its entry
head is restored before parsing. There is no extra seal-read leaf.
The actual source74 $h=e+2$, $m=e+1$ at this first import, so Save,
Scan, Home and Restore have respectively $h,m,m+1,h$ move/iteration
counts; the word helper costs still use the actual larger banks.

All assignments and tests include their actual $r_B$-field Base, dry/real
emission, separators/F/seals, descriptors, parity and Field scans, as
specified in Proposition4.4. Export/staging include the measured two
initial fields and the one descriptor stage, copied exactly once at its
defined level. Boundary/Prefix/locator/Issue/Call include every75-case
row lookup, local update, represented receipt/event and stop/range test.
Body algorithms include all component, role, record, parser, countdown,
reselection, re-encoding and comparison leaves. Every publication includes
its actual setup, both copies, print, callback import/check, ACK and held
resource return. All original00 work is the actual unchanged CAP route.
These lists together with ARC10.2's unchanged leaves determine the bill
at every finite cut; they contain no unnamed selector/decoder/compiler
service constant.

**Proposition 7.2 (native counts).** The local first-load fragment has
$7e+6$ rows, $e$ actual IN bits, $e$ new target finite bits and $e+1$
new ordinary74 cells. Relative to the old $4e+2$ first fragment its row
increment is $3e+4$. The two74 boundaries, all paid $H_B$/owner/phase/
cursor bits and their installation rows are additional original boot
work. For every finite actual prefix,

$$
(\mathrm{ticks},\mathrm{fee},\mathrm{bits})
=(n,2n,S_{\rm irreducible,B}+b_{\rm ctl}+8A+8n),
\qquad n=\sum_{o,p}N_{o,p}.
$$

Proof. Definition2.2 has seven executed rows per bit and six end rows;
only $X_j,X_e$ allocate ordinary74 cells and only $C_j$ construct first
target bits. Its control table and rights were installed earlier, so
their costs are not counted twice in this subtotal. For their earlier
installation let $k_B$ be the length of the finite literal initial
control/token encoding obtained from the original boot with $H_B$ and
these added fields. Its actual five-state bitwise installer has
$4k_B+2$ occurrences, with any original boundary/input/preparation work
outside that bit-store fragment counted by its own leaves. $k_B$ is
the length of a fully specified finite encoding, not free endowed code
or an unmeasured runtime constant. Irreducible primitive control remains
the declared finite foundation only. All later first/second stores remain
retained in $b_{\rm ctl}$.

Induction over each actual leaf yields Definition7.1's increments.
Summing gives the displayed full vector and storage equation, including
all dead banks, raw partial words, old versions, actual and represented
receipts, initial mirrors/copies and the original final consumer.
The actual eight payload lengths retain the existing disjoint copy/print
subtotal $17(L_C+L_P+L_I+\sum_{s=0}^4L_s)+56$, with all other leaves
additional. This is no numeric benchmark or optimum assertion. ∎

**Definition 7.3 (75-port local patches).** Use the sole storage outer
$F_{76}$ with75 tape trees and finite component $F_{q_B}$. Enumerate
UAS2.3's actual finite raw patterns using the complete codec/catalog of
Definition4.1 and all rows/effects of §2 and the expanded main. For each
case list core cells/neighbors, each named marker effect in order, then
the meter append cell as $\mathcal D_i$; core and receipt append sites
as $\mathcal A_i$; old head-slot routes in port/lane order as
$\mathcal J_{i,\mathrm{old}}$; and fresh finite sockets as
$\mathcal Z_i$. Retain repeated inspections. Combine aliased target bits
once, in first-role/track order, preserving ordered final effects.
Use the actual root/socket routes for this new scaffold; do not reuse
the numerical routes of $F_{75}$. Every finite alternative and maximum
local footprint is finite for this fixed apparatus.

**Proposition 7.4 (local lift and exact structural bill).** These patches
have simultaneous native enabledness, identical event/receipt and the
same raw successor under the new unary representation, at every actual
raw cut. For $C=2+A+n$ constructed tape cells and $c$ present finite bits,

$$
V_B=149+2q_B+c+24C,\qquad L_B=75+q_B+8C.
$$

Their exact row and full structural costs are GENERAL21.14's displayed
$p_i^{\rm st},v_i,w_i,g_i$ with these actual lists, and

$$
\rho_B+1+8(197+2q_B+c_0)+\sum_{i=1}^n g_i.
$$

Proof. Definition4.1's local cores and finite effects are exactly the
ones enumerated. UAS's unary old-bit, absent-bit, cell-append and head-link
templates produce those same final tracks. In particular ordinary WR74
has an existing cell, WRITE$_L$ has an absent finite socket, and a seal
CTL has a designated marker assignment, with no seal-read role. Receipt
aliases preserve the new meter read mark as in Lemma4.2. Their finite
pattern table therefore gives the claimed local square, including wrong
raw input without promising its recovery or termination.

A $k$-cell tape has $24k+1$ vertices/$8k+1$ terminals. Seventy-five tapes,
the $2q_B-1+c$ finite component and75 outer internal vertices give the
two formulas. At the irreducible entrance $C=2$, so the vertex count is
$197+2q_B+c_0$. Charge its seven initialized slots and each birth plus
commit, giving $1+8V_{B,0}$; the fixed finite rule apparatus $\rho_B$
is additional. Cell inspection still costs68, finite-component
inspection $6q_B+3c-4$; changed outer paths enter their actual route
lengths. Each designated old bit has three assignments, each new cell
24 vertices, each new finite bit one, head retarget/activation three/two.
Empty/no-op assignments remain charged. These disjoint lists give
$v_i=24e_i+s_i$ and
$w_i=3t_i+2e_i+2s_i+3r_i+2a_i+7v_i$, then
$g_i=1+p_i^{\rm st}+w_i+v_i$. Summation is on this one actual run.
No old74-port foundation or stencil constant is transferred unchanged. ∎

## 8. Mathematical scope of the refinements

**Proposition 8.1 (scope and reuse).** The added content is the explicit
active mirror bootstrap, its disjoint closed74 importer and actual75-port
joins consumed in GENERAL21's acquisition/use proof. The retained-input
pair and canonical failure remain GENERAL11–13's existing results;
geometric/chronological codecs, the bank construction, binding arithmetic
and positioned channel method remain their cited suppliers. None of
these refinements changes a published original-$Q$ claim.

Proof. The actual first input reaches74 by Definition2.2's ordinary
writer path, reaches bootWitness by Theorem3.2's actual reader path,
reaches immutable bindings by Theorem5.1, and is consumed by Lemma5.3
and Corollary6.3. Independent bodies use Theorem6.1's own data. The
local and compiled correspondence relations in §4 specify exactly which
supplier operations have unchanged footprints and which require new
instances, without identifying full old/new runs. Theorem6.2 preserves
the actual verifier/INITIAL consumer, rather than renaming an Image as
that consumer's target. Propositions7.2/7.4 retain every same-run cost.

The arguments are repo-derived mathematical source proofs under the
declared native and stronger atomic-incidence primitives. The abstract
NativeSerialMachine, NativeFullSourceProducer, NativeSerialEffective,
TypedFiniteViewKernel, PredictiveMemoryMinimalQuotient and
RealizedImageKernelFactorization interfaces retain their run,
realization/readout/update/fibre premises. No such abstract interface
grants74 rights, supplies $H_B$, or makes an unproved operation available.
GENERAL22's separately pinned library simulation/encoding statements
and its Rushby background remain background; no external security or
unwinding theorem is instantiated by this local construction.

There is no new Lean verification or lower physical implementation.
Unknown-source/generic initialization, arbitrary raw post-DONE recovery,
unfinished-flight/busy-cut acquisition, global original-$Q$ correspondence,
final00/posthalt historical coverage, uniform bounds, minimal-port or
optimal-resource claims and the full four-expression programme remain
unresolved in their original scopes. Finite pointwise completion of the
named domain does not settle any of those larger obligations. ∎

## 追加锚（本行以下为增补区）
