# Finite transducers for the zero-leakage partition reduction

This volume supplies word and machine obligations for Theorem 4.3 of
[PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md](https://github.com/the-omega-institute/trureturing/blob/488e3fce13cd3f77e9051ae316dadc0da7f7a4fc/docs/develop/theory/PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md).
The standing finite-dimensional, support and natural-logarithm conventions are
its Sections 1.2 and 3.1-3.4. The current main-volume presentation is Section 6.4
of SYMPLECTIC_PREDICTIVE_COMPLETION.md.

## 1. Original physical reduction and finite response processing

**theorem 1.1 (Full original partition reduction).** For every explicit universe
of n Boolean variables and every list F of m clauses of length at most three,
the raw violation projectors give the same Hamiltonians
$$
H_F=(n+1)\sum_{j=1}^m\Pi_j,\qquad
H=|1\rangle\langle1|\otimes I+I\otimes H_F,\qquad
\beta=\log2.
$$
The projectors are Hermitian, diagonal, pairwise commuting and supported on at
most three variables, including empty, repeated and tautological clauses.
The full complex matrix exponential and trace satisfy
$$
\#\mathrm{SAT}(F)=\left\lfloor\frac23\operatorname{Tr}e^{-\beta H}\right\rfloor.
$$
A single exact query with a succinct local-term descriptor and ordinary reduced
positive binary rational response suffices, using fixed finite pre- and
post-machines with polynomial running time. The independent standard count is
over the appearing binary variable names. Dense renaming gives the explicit
universe; in the reverse correspondence a tautology for each declared variable
preserves unused variables. Those tautologies do not enter the physical clauses.
Malformed source words use the zero-variable one-empty-clause Hamiltonian,
whose partition is 3/4 and whose recovered count is zero. The visible algebra
has zero leakage and exact prediction for every joint state and time. The same
centered local Hamiltonians give product Gibbs normalization and zero
support-aware recovery defect for every visible state, including singular
states. The zero-variable hidden singleton is treated directly. No efficient
Gibbs preparation, fixed geometry, bounded interaction strength or approximate
hardness is asserted.

**theorem 1.2 (Ordinary dyadic response transducer).** There is a fixed finite
four-stack machine with alphabet {0,1,/}, eleven labels and twenty-four internal
states. On a positive canonical numerator word for p and denominator word
1 followed by e zeros, if 3 divides p and either e=0 or p is odd, it clears the
input and all work stacks, resets its finite state and emits canonical binary
digits for
$$
\begin{cases}
2(p/3),&e=0,\\
\lfloor (p/3)/2^{e-1}\rfloor,&e>0.
\end{cases}
$$
Its real transition count is bounded by a fixed linear polynomial in the whole
ordinary response length. It reads the separator and denominator; no annotated
shift, cut or exponent is supplied. The division state is one of 0,1,2, each
denominator shift is an actual stack mark, and the output zero is one symbol.
Malformed or unsuitable words emit zero after clearing all work stacks.

**theorem 1.3 (Total raw clause codec).** Source mode accepts exactly words
$$
1^n0\,(01\,(11\,b\,1^i0)^{\leq3}\,10)^m\,00,
$$
with each literal index i strictly below n. Physical mode additionally has
prefix 11, the fixed beta and visible tokens 00 and 01, and coefficient
1^(n+1)0 immediately after every clause tag. For every Boolean word, each
mode is a total option-valued decoder. It returns exactly universe n and raw
formula F if and only if the word is their complete encoding and every clause
has at most three literals. No external decoding witness is supplied. The
accepted encoding is unique, including n=0, empty formulas and clauses,
repeated and tautological literals, and unused declared variables. Physical
coefficients and the complete trailing delimiter are checked by the decoder.

**theorem 1.4 (Machine error entry cleanup).** For every finite control state
and arbitrary Boolean contents of input, header, scratch and partial-query
stacks, the fixed pre-machine starting at badInput with empty output reaches
the exact haltList configuration for the valid zero-variable one-empty-clause
dummy query. It resets the finite control and empties all four starting stacks.
The actual step count is bounded by the sum of their lengths plus five. This
error-entry theorem does not assume that the stacks contain unary marks. The
complete parser-to-error-entry bound for every malformed source word is a
separate obligation.

## Append Anchor

## 2. Exact clause preprocessing on all words

Fix the source and physical word conventions of Theorem 1.3 and the same
five-stack pre-machine used in Theorem 1.4. Its alphabets are Boolean, its
nineteen labels and thirty-six control states are fixed independently of the
input, and its initial and terminal configurations have empty work stacks and
reset control. Write $s(F)$ and $q(F)$ for the complete source and physical
encodings of a raw formula $F$, respectively. Let $P$ be the fixed program's
output-push bound, obtained by summing the statement push bounds over its
finite labels, as in `programPushBound`.

**theorem 2.1 (Valid source execution and exact output length).** For every
$n\in\mathbb N$ and every raw formula $F$ over $n$ declared variables, if each
clause has length at most three, the fixed pre-machine started on $s(F)$ reaches
the exact clean terminal configuration with output $q(F)$ in at most

$$
3(|s(F)|+3)^2+7
$$

actual transitions. The output length is exactly

$$
|q(F)|=|s(F)|+6+|F|(n+2).
$$

The declared universe includes unused variables. Empty formulas, empty clauses,
repeated literals and clauses, tautologies and $n=0$ remain allowed.

**theorem 2.2 (Total raw-input clock and output growth).** For every Boolean
word $w$, without any syntax premise, there is a word $o$ such that the same
fixed machine reaches its exact clean terminal configuration with output $o$
within $b(|w|)$ actual transitions, where

$$
b(L)=(4L+20)L+13.
$$

Its output satisfies $|o|\le b(|w|)P$. This clock statement does not identify
the output or infer acceptance from it.

**theorem 2.3 (All-input output refinement and actual rejection prefix).** Let
$D_s(w)$ be the total source decoder. Define $F_w$ to be its decoded universe
and raw formula when decoding succeeds, and to be the zero-variable formula
with one empty clause when decoding fails. Let $Q_w=q(F_w)$ in the successful
case and let $Q_w$ be the fixed dummy query in the failed case. For every raw
Boolean word $w$, the fixed pre-machine reaches the exact clean terminal
configuration with output $Q_w$ within $b(|w|)$ transitions. The physical decoder
returns exactly $F_w$ on $Q_w$, the output is the complete physical encoding of
$F_w$, all its clauses have length at most three, and
$|Q_w|\le b(|w|)P$.

If $D_s(w)$ fails, its actual run has a prefix of at most $b(|w|)$ transitions
reaching `badInput` with empty output and some concrete input, header, scratch
and partial-query stack contents. Theorem 1.4 then applies to that configuration.
A valid source encoding for the zero-variable formula with one empty clause
also emits the same dummy query: acceptance and rejection are distinguished by
the source decoder and the actual error prefix, rather than by output equality.

## Append Anchor 2


## 3. Ordinary physical rational responses

For a raw clause family $F$ over $n$ declared Boolean variables, let
$H_F=(n+1)\sum_{c\in F}\Pi_c$ and
$H=|1\rangle\langle1|\otimes I+I\otimes H_F$, with the original raw-clause
violation projectors. Write
$Z_F=\operatorname{Tr}(\exp(-\log(2)H))$ for the full complex trace.
The independently defined satisfying count counts assignments to all $n$
declared variables using the ordinary CNF evaluation.

A physical response word for $F$ is the ordinary binary numerator, one slash,
and the ordinary binary denominator of a positive reduced rational $r$ whose
complex cast equals $Z_F$. Both fields have no leading zero, and the denominator
one is explicit. This definition imposes no count, divisibility or dyadic
condition on the response.

**theorem 3.1 (Unique physical response and actual count recovery).** For every
$n\in\mathbb N$ and every raw clause family $F$ over $n$ variables, there is a
unique physical response word $w$. Put $K=(n+1)|F|$. The word satisfies

$$
|w|\le n+2K+5.
$$

It is arithmetically suitable in the sense of Theorem 1.2: its numerator is
divisible by three, its denominator is $2^e$, and its numerator is odd when
$e>0$. The fixed four-stack postprocessor reaches the exact clean terminal
configuration for its total word output in at most $3|w|+10$ transitions.
The ordinary binary value of that output is exactly the independently defined
satisfying count of $F$.

Indeed, write $S=\sum_a2^{K-(n+1)v_F(a)}$. The full trace identity gives
$Z_F=3S/2^{K+1}$, and $0<S\le2^{n+K}$. Rational normalization gives a common
positive natural factor $c$ with $3S=pc$ and $2^{K+1}=qc$. The prime-power
divisor law implies that $q$ is a power of two and $3$ does not divide $c$;
hence $3$ divides $p$. Reducedness gives oddness of $p$ when $q>1$.
The inequalities $p<2^{n+K+2}$ and $q<2^{K+2}$ bound the two ordinary binary
fields. Injectivity of the rational-to-complex cast proves uniqueness.
The postprocessor's actual arithmetic output equals
$\lfloor(2/3)\operatorname{Re}Z_F\rfloor$, which is the count by the physical
recovery identity. The denominator-one branch uses actual doubling, and the
positive-exponent branch uses actual low-bit truncation.

The zero-variable one-empty-clause query has response `11/100` and output zero;
the zero-variable empty formula has response `11/10` and output one. Empty,
repeated and tautological clauses and unused declared variables are retained.
The rational response statement does not identify arithmetic suitability with
physical validity or replace the conventional appearing-name encoding problem.

## Append Anchor 3


## 4. A paid one-query operational protocol

The source word is a raw Boolean word in the unary declared-universe grammar.
For a word $w$, let $L=|w|$. Total preprocessing selects its parsed formula
when parsing succeeds and the zero-variable one-empty-clause formula otherwise.
Denote this formula by $F_w$ and its actual emitted physical query by $q_w$.
A valid source can itself describe the fallback formula; the query value does
not identify acceptance or rejection.

The protocol consists of actual preprocessing transitions, a query handoff,
one physical ask, an external read-only response stream, ordinary response
writing and reversal, actual postprocessing transitions and a terminal handoff.
The stream is outside finite control and the ordinary writable stacks. Reading
one stream symbol costs one transition and loads only that symbol into finite
control. A separate transition of a fixed four-stack, two-label materialization
machine pushes it. Its real reversal transfers the completed word onto the
postprocessor input stack. The subsequent handoff preserves those stack
contents and changes only the finite label and control. Each protocol edge,
including a handoff and the ask, has unit cost.

**theorem 4.1 (All-input paid execution with one ask).** For every raw Boolean
source word $w$, there is a physical response $r$ to $q_w$ such that

$$
|r|\le 2(L+1)^2+L+5.
$$

The ordinary binary value of the total postprocessor output on $r$ is the
independently defined satisfying count of $F_w$. From the exact clean
preprocessor initialization on $w$, the protocol reaches the exact clean
postprocessor halt on that output in at most

$$
16L^2+50L+71
$$

edges, with exactly one ask. Every complete protocol run from that
initialization to a terminal configuration also has exactly one ask.

To obtain the response bound, source-codec soundness gives $n\le L$ and
$|F_w|\le L+1$ on accepted words. These inequalities also hold for the rejected
fallback. The physical representation bound of Theorem 3.1 then applies.
For a response of length $R$, actual read, push and reversal execution plus
its two handoffs costs $3R+3$ edges. Adding the preprocessing bound
$(4L+20)L+13$, the query handoff, one ask, the postprocessing bound $3R+10$
and the terminal handoff gives the displayed quadratic bound. The exact-one
property follows from a phase invariant: before the ask the phase indicator
is zero, after the ask it is one, and its difference over any run equals
the number of ask edges.

This statement uses the explicit variable universe decoded from the unary
source. The conventional appearing-binary-name dictionary converters and their
count-preserving word execution correspondence remain separate obligations.
The protocol is an operational composition of fixed native machines and an
explicit physical response port; it does not assert a compiled single FinTM2
oracle-program implementation of the entire phase relation.

## Append Anchor 4

## 3.2. Complete native response execution

**theorem 3.2 (Native suitable-response execution).** For every Boolean numerator tail xs and every natural e, let p be the ordinary binary value of the leading-one word 1::xs and let w be that numerator, one slash, and the denominator 1 followed by e zeros. If three divides p and p is odd whenever e>0, the fixed four-stack ternary post-machine runs from its exact initialization on w to the exact clean halt for the binary responseOutput xs e in at most 4|w|+4 actual transitions. The ordinary value of that output is 2(p/3) when e=0 and (p/3)/2^(e-1) otherwise, where natural division discards the remainder. The denominator-one branch permits even numerators. All scratch stacks are empty and control is reset at this halt.

**theorem 3.3 (Arbitrary post-error entry).** For every one of the twenty-four post-control states and every arbitrary ternary input, quotient and shift-stack contents, the fixed post-machine at badInput with empty output reaches the exact clean halt containing the one-symbol zero in at most the sum of those three stack lengths plus three actual transitions. All three starting stacks are emptied and control is reset; no unary or Boolean scratch-content premise is imposed.

**theorem 3.4 (Total ordinary response refinement).** For every raw ternary word w, define O(w) by scanning its actual leading-one numerator, remainder and quotient, requiring a slash followed by a leading-one denominator and an all-zero complete suffix, selecting doubling at exponent zero and right shifts otherwise, and returning the one-symbol zero on syntax or arithmetic faults. The fixed post-machine reaches the exact clean halt for binaryWord(O(w)) from exact initialization on w in at most 3|w|+10 actual transitions. For every xs and e whose ordinary response equals w, if three divides the leading-one numerator value p and p is odd whenever e>0, the numeric value of O(w) is 2(p/3) at e=0 and (p/3)/2^(e-1) at e>0, with natural division. Suitability means existence of such xs and e with those arithmetic conditions. If w is unsuitable then O(w) is the one-symbol zero; every output is that zero or begins with one. A suitable word can also produce zero, so zero output is not an acceptance characterization. The clock includes fault detection and scratch cleanup, with no supplied parse, exponent or execution certificate.

## Append Anchor Response

## 5. Raw physical matrices and complete response execution

**theorem 5.1 (Full raw-clause physical identities).** For every natural n and every finite list F of raw Boolean clauses over the explicit universe Fin n, put d=2^n and let v_F(a) count the violated clauses of assignment a. Let each Pi_c be the diagonal violation projector, P=diag(0,1), H_F=(n+1)sum_c Pi_c, H=P tensor I+I tensor H_F, and S=sum_a 2^((n+1)(|F|-v_F(a))). At beta=log2 the actual complex exponential trace is Z=3S/2^((n+1)|F|+1), and floor((2/3)Re Z) equals the ordinary CNF satisfying count over every declared assignment. H_F and H are Hermitian; each clause projector is Hermitian and idempotent, depends only on a variable set of cardinality at most its literal length, all clause projectors commute, and the empty-clause projector is I. With H_A=P-I/2 and H_B=H_F+I/2, the normalized centered visible partial trace of H is H_A, half its visible-factor partial trace is H_B, and H=H_A tensor I+I tensor H_B. For every complex visible matrix M, [H,M tensor I]=[P,M] tensor I and its normalized visible conditional-expectation residual is zero. For every real time t and every complex joint matrix R, the actual evolution U=exp(-itH) satisfies Tr_B(U R U*)=U_A Tr_B(R) U_A*, where U_A=exp(-itH_A). Define Gamma(K)=exp(-beta K)/Tr(exp(-beta K)). The actual full Gibbs state is Gamma(H_A) tensor Gamma(H_F), Gamma(H_A)=Gamma(P), Gamma(H_B)=Gamma(H_F), and the hidden marginal is Gamma(H_F); if n=0 that hidden state is the singleton identity. For every visible density state rho, including singular states, its support is contained in Gamma(H_A), the support of rho tensor Gamma(H_F) is contained in Gamma(H), its visible marginal is rho, its extended support-aware relative entropy against Gamma(H) equals that of rho against Gamma(H_A), the corresponding finite trace-log difference is zero, and its extended relative entropy against itself is zero. All these identities use the identical H and H_F, without an assumed partition/count certificate or full-rank hypothesis on rho.

## Append Anchor 5
## 6. Conventional binary names and actual dictionary routines

A conventional name is a positive most significant bit first binary spelling.
Its word representation replaces each bit $b$ by the pair $1b$ and appends a
zero terminator. Write $E(a)$ for this escaped representation of a Boolean
word $a$, and define the dictionary stream of a list $D$ of names by

$$
S(D)=E(\operatorname{rev}(D_1))\cdots E(\operatorname{rev}(D_{|D|})).
$$

The conventional clause word has a clause prefix `01`, a literal prefix
`11` followed by its Boolean polarity and escaped name, a clause terminator
`10`, and a final formula terminator `00`. Each clause has at most three
literals. Names have leading bit one. There is no declared variable-universe
header. The independently defined count ranges over Boolean assignments to
exactly the distinct names appearing in the parsed clauses, evaluates the
ordinary CNF, and assigns zero to malformed words. The empty formula has one
assignment, and an empty clause rejects every assignment.

**theorem 6.1 (Whole-name comparison with literal restoration).** For every
pair of Boolean words $a,b$, every previous output word $o$ and every caller
frame $f$, the fixed six-stack, four-label comparison machine starts with
operands $a,b$, empty operand backups, output $o$ and frame $f$. Within

$$
2(|a|+|b|)+4
$$

transitions it reaches its terminal label and reset control with operands
exactly $a,b$, empty backups, output $\operatorname{decide}(a=b)::o$ and the
unchanged frame $f$. This includes unequal operand lengths, empty words and
arbitrary spellings. The routine consumes and saves actual bits during
comparison and restores them with actual stack transfers.

**theorem 6.2 (Paid lookup with the restored dictionary and first index).**
For every Boolean query word $q$, every list $D$ of Boolean name words and
every frame $f$, the fixed nine-stack, twelve-label lookup machine starts
with query $q$, stream $S(D)$, frame $f$ and all other stacks empty. It
reaches its terminal label and reset control within

$$
(2|q|+12)|D|+4|S(D)|+3
$$

transitions. The query and the entire dictionary stream are restored
literally, the frame is unchanged, and all candidate, comparison, backup
and history stacks are empty. The index output is the membership flag
$\operatorname{decide}(q\in D)$ followed by $\operatorname{idxOf}(q,D)$ true
symbols. Here the index is the first match and is $|D|$ when no match exists;
dictionary repetitions are permitted. Extraction, comparison, candidate
draining and stream restoration are ordinary charged machine transitions.

**theorem 6.3 (Rightmost dictionary construction with a quadratic clock).**
For every list $A$ of Boolean name words, every frame $f$ and every dimension
suffix $d$, the fixed eleven-stack, twenty-one-label builder starts with
source stream $S(\operatorname{rev}A)$, dimension suffix $d$, frame $f$, and
empty dictionary, index, comparison and backup stacks. Within

$$
20(|S(A)|+1)^2
$$

transitions it reaches its terminal label and reset control. Its dictionary
stream is exactly $S(\operatorname{dedup}A)$, where deduplication retains
rightmost occurrences in their original relative order. Its dimension
stack is $|\operatorname{dedup}A|$ true symbols followed by exactly $d$.
The frame remains $f$; the source, index, candidate, comparison, operand
backups and history stacks are empty.

The builder scans occurrences from right to left, invokes the actual lookup
routine, consumes its membership flag, and either drains the already-present
name or inserts its escaped reversed spelling at the head of the dictionary.
Each insertion pushes one dimension symbol. The proof follows these actual
branches and charges extraction, lookup, index draining and writing; the
quadratic estimate bounds the resulting sum of phase clocks. All stack
alphabets are Boolean, and the builder has 108 possible finite controls,
independent of the occurrence list and name lengths.

**theorem 6.4 (All-input conventional parsing with restored source).**
For every raw Boolean word $w$ and every caller frame $f$, the fixed
five-stack, four-label, 792-control parser starts with source $w$, frame
$f$ and empty saved, occurrence and result stacks. Within

$$
4|w|+5
$$

transitions it reaches its terminal label and reset control with source
exactly $w$, empty saved stack and unchanged frame $f$. Its result stack is
one Boolean symbol, true exactly when the total conventional decoder
returns a formula $F$. In that accepted case its occurrence stack is

$$
S(\operatorname{rev}(\operatorname{occurrences}F)).
$$

On rejection the occurrence stack is empty. Thus incomplete tags or names,
a leading-zero name, a fourth literal, truncation and trailing symbols
enter the actual occurrence cleanup branch; every consumed source symbol is
restored onto its untouched suffix. Occurrences on accepted words are
written with real pushes while the finite grammar control scans the input.

These are routine boundaries: comparison and lookup retain their operand
words, and parsing retains the complete raw source. They are the operational
components for dense-name conversion. Assignment transport, clean complete
forward and reverse word conversion, and their composition with the paid
physical protocol require the further converter execution statements.

## Append Anchor 6

## 7. Paid count-preserving clause word converters

The conventional source alphabet is Boolean. A variable name is a nonempty
most-significant-bit binary word whose first bit is one. Literal and clause tags
use the whole-word conventional grammar of Section 6: clauses have at most three
literals, names are escaped, and the final formula tag consumes the entire word.
The assignment universe consists exactly of the distinct appearing name words,
without declaring names of smaller numerical value. Write $C(w)$ for the number
of assignments satisfying the decoded ordinary CNF; set $C(w)=0$ when the total
decoder rejects $w$. This count uses ordinary CNF evaluation alone.

**theorem 7.1 (Paid dense forward conversion).** There is one fixed finite
Boolean stack machine $D$ such that, for every raw conventional word $w$ of
length $L$, its clean initial configuration reaches its clean halted
configuration with output $u(w)$ in at most

$$
80(L+1)^2
$$

actual machine transitions. The output satisfies

$$
|u(w)|\le L^2+8L+7.
$$

Its total unary decoder succeeds with an explicitly declared universe and a
formula $F(w)$ all of whose clauses have width at most three. The ordinary CNF
count on that entire explicit universe equals $C(w)$. On accepted source words,
the universe is the length of the occurrence dictionary formed by retaining
rightmost occurrences in their original relative order. Each original literal
is relabeled by its first dictionary index. On rejected words the output is
source0011000, the valid zero-variable one-empty-clause formula, with count zero.
A valid conventional empty-clause word can have that same output, so output
equality alone does not identify rejection.

The fixed program translates the whole-word parser, paid dictionary builder
and restored lookup instruction by instruction. Dimension symbols, candidate
names, occurrence stream, dictionary, literal indices, backups and output
occupy ordinary stacks. Its execution proof follows the source grammar and
actual transfer loops, includes all restoration and output growth, and ends
with every non-output stack empty and initial control restored. The dictionary
bijection transports assignments; literal relabeling preserves ordinary CNF
evaluation, including repeated variables and opposite polarities. No decoder
certificate, externally supplied dictionary run, or input-dependent control is
an input to the machine or theorem.

**theorem 7.2 (Paid reverse conversion with declared unused variables).** There
is one fixed finite Boolean stack machine $R$ such that, for every raw unary
source word $w$ of length $L$, its clean initial configuration reaches a clean
halt with conventional output $v(w)$ in at most

$$
10L^2+41L+33
$$

actual transitions, and

$$
|v(w)|\le 4L^2+14L+6.
$$

Let $E(w)$ be the independently defined ordinary CNF count of the formula on
its entire explicit universe when the unary whole-word decoder succeeds, and
zero when it rejects. Then the conventional whole-word decoder succeeds on
$v(w)$ and $C(v(w))=E(w)$. For an accepted $n$-variable formula $F$, the output
renames variable $i$ to the canonical binary word consisting of a one followed
by $i$ zeros, and appends the clause $x_i\lor\neg x_i$ for every $i<n$. Thus every
declared variable appears, even when absent from $F$, and the appearing-name
assignment universe is in bijection with all $n$ declared variables. Empty
formulas, empty clauses, $n=0$, repeated literals and tautologies are included.
On rejection the conventional output is011000, one empty clause on the empty
appearing universe, with count zero. Valid unary source0011000 also reaches that
output.

The reverse program executes the actual unary preprocessor, scans and removes
query coefficients, writes binary names, restores its unary index counter,
appends the tautology clauses, reverses the result and clears all scratch
stacks. The explicit unary header pays for dimension-dependent work and output.
The appended tautologies belong only to the conventional consumer converter;
they do not alter the original raw physical clauses, Hamiltonian or partition
function. Both converter results concern ordinary word execution and assignment
transport. Their further paid composition with the physical oracle retains the
same raw clause Hamiltonian and is a separate operational claim.

## Append Anchor 7

## 8. Conventional word execution through the physical query

**theorem 8.1 (Paid conventional physical query and ordinary count recovery).**
Use the independent appearing-name convention of Section 7. For every raw
Boolean source word $w$, let $L=|w|$, $B=L^2+8L+7$, and let $F(w)$ be the total
densely prepared explicit-universe formula. The fixed finite query compiler
executes actual dense naming, pays for transferring its output to the unary
query constructor, and reaches the exact clean query configuration for the raw
clauses of $F(w)$. Its twenty-three Boolean stacks, labels and finite control are
fixed independently of $w$.

The physical phase has a response word $r$ satisfying exactly the positive
rational trace relation: for some $z\in\mathbb Q$,

$$
z>0,\qquad z=\operatorname{Tr}\exp[-(\log 2)H_{F(w)}]
$$

under the complex embedding, and $r$ is the canonical reduced binary numerator,
slash and denominator of $z$. This relation has no clause-count, dyadic,
divisibility or arithmetic-suitability hypothesis. The denominator is spelled
explicitly even when it is one. The response obeys

$$
|r|\le 2(B+1)^2+B+5.
$$

There is an actual complete counted trace from the compiler's clean input to
the postprocessor's exact clean halt, using that response, of length at most

$$
80(L+1)^2+20B^2+72B+87.
$$

The trace performs precisely one distinguished physical Ask. It reads the
external response stream symbol by symbol, writes every symbol to ordinary
stacks, reverses the written word and executes the fixed four-stack
postprocessor. The most significant bit first ordinary output represents
$C(w)$, the independently defined satisfying assignment count of the raw
conventional word. Every complete trace starting at this same clean input has
exactly one Ask, not merely the constructed witness trace.

Malformed sources pass through the valid zero-variable one-empty-clause
physical query and still perform one Ask. A valid empty-clause source may
produce that same query. Acceptance is therefore determined by the source
decoder and execution phase, never by equality with the fallback query. The
Hamiltonian in this trace uses the original densely renamed raw clauses with
coefficient $n+1$, the full visible factor $3/2$, and inverse temperature
$\log 2$. The reverse converter's unused-variable tautologies do not enter the
physical clauses. The direct clock follows actual finite instructions and
paid transfer loops; it does not assume a general polynomial composition
principle or instantaneous response loading.

## Append Anchor 8

## 9. Exact paid phase boundaries of the finite converters

Use the escaped names, rightmost dictionary, ordinary clause grammar and
independent total decoders of Sections 6 and 7. All words are most significant
bit first Boolean lists. An execution bound counts applications of the actual
fixed machine step. A clean halt has the output on its designated stack, every
other stack empty, the initial finite control restored and no remaining label.

**theorem 9.1 (Translated parser endpoint and accepted source spelling).**
For every raw conventional word $w$, the eighteen-stack dense converter, from
its clean initialization, reaches its parser-return label within $4|w|+5$
transitions. Its control is the reset dense-word control. The translated parser
stacks contain the restored source $w$, an empty saved stack, an empty caller
frame, the occurrence stream $S(\operatorname{rev}(\operatorname{occurrences}F))$
when the total conventional decoder returns $F$ and the empty stream otherwise,
and the singleton acceptance flag. All stacks outside the translated parser
are empty. For every formula $F$ accepted by that decoder, the whole original
word is exactly its conventional formula encoding, and every clause of $F$
has length at most three. This is a parser phase endpoint of the actual dense
converter; the caller frame is empty.

**theorem 9.2 (Complete dense execution with the explicit phase clock).**
For every raw conventional word $w$, the fixed eighteen-stack dense machine
reaches its clean halt with output $u(w)$ defined in Theorem 7.1. Write $L=|w|$.
On decoder rejection its clock is $5L+15$. On acceptance of $F$, put
$d=\operatorname{dedup}(\operatorname{occurrences}F)$ and
$s=|S(\operatorname{occurrences}F)|$. Define the literal and clause clocks by

$$
\begin{aligned}
t_d(a,\epsilon)
 &= (2|a|+12)|d|+4|S(d)|+3+4|a|
    +\operatorname{idxOf}(a,d)+8,\\
t_d(c)&=\sum_{\ell\in c}t_d(\ell)+4.
\end{aligned}
$$

The complete accepted execution is bounded by

$$
4L+5+1+20(s+1)^2+(|d|+1)
 +\left(\sum_{c\in F}t_d(c)+2\right)
 +(|S(d)|+1)+(|u(w)|+1).
$$

The accepted decoder also implies $w$ is exactly the conventional encoding
of $F$ and every clause of $F$ has length at most three. The clock includes
the actual parser return, rightmost dictionary construction, dimension output,
restored name lookup, index writing, dictionary draining and output reversal.
Rejection drains its actual remaining source and emits the valid zero-variable
one-empty-clause unary source. This execution statement does not by itself
assert the assignment-count correspondence of Theorem 7.1.

**theorem 9.3 (Complete reverse execution with the explicit phase clock).**
For every raw unary word $w$, let $(n,F)$ be its total prepared explicit-universe
formula: the decoder's formula on acceptance and the zero-variable
one-empty-clause formula on rejection. Let $v(w)$ be the conventional output
of Theorem 7.2. The fixed ten-stack reverse machine reaches its exact clean
halt with output $v(w)$ within

$$
(4|w|+20)|w|+13
 +\sum_{c\in F}\left(n+6+\sum_{(i,\epsilon)\in c}(i+4)\right)
 +2+n(n+3)+2n+6+|v(w)|
$$

actual transitions. The execution includes the complete total unary
preprocessor, coefficient removal, canonical binary name writing, restored
index counters, one tautology for every declared variable and output reversal.
Those tautologies occur only in $v(w)$; they do not enter the raw physical
formula. This statement supplies the actual execution before the decoder and
assignment-count refinement of Theorem 7.2.

**theorem 9.4 (Clean dense-to-query compiler and decoded count).**
For every raw conventional word $w$, set $L=|w|$ and $B=L^2+8L+7$. The fixed
twenty-three-stack Boolean query compiler reaches its clean halt with output
the unary preprocessor's prepared query for $u(w)$ within

$$
80(L+1)^2+4B^2+22B+15
$$

actual transitions. The total physical-query decoder accepts that exact output
as the densely prepared explicit-universe formula $F(w)$. Its ordinary CNF
count on the whole declared universe equals the independent conventional
appearing-name count $C(w)$. The transfer from the dense output stack to the
preprocessor input is paid symbol by symbol in two actual reversal loops.
Malformed $w$ therefore reaches the valid zero-variable one-empty-clause
physical query with count zero. A valid empty-clause source may have that same
output. This is the complete deterministic prefix before the physical Ask;
the response and full trace bounds are those of Theorem 8.1.

## Append Anchor 9
