using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class SharpFiniteAlphabetOneRecutDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => DefinitionDsl.Id(n);
    private static Formula All(string n, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Exists(string n, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula And(params Formula[] ps) =>
        ps.Aggregate((p, q) => new Formula.Logic(p, FormulaLogicOperator.And, q));
    private static Formula Imp(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula s) => Call("Member", x, s);
    private static Formula Fin(Formula s) => Call("Finite", s);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Pow(Formula x, Formula y) => Seq(Open, x, Close, Caret, Grp(y));
    private static Formula Words => Call("List", V("A"));
    private static Formula Languages => Call("Set", Words);
    private static Formula Pairs => Call("Prod", Languages, V("A"));
    private static Formula R(Formula c, Formula k) => Call("residualSet", c, k);
    private static Formula Q(Formula c, Formula k) => Call("oneBoundary", c, k);
    private static Formula F(Formula c, Formula k, Formula e) => Call("currentFiber", c, k, e);
    private static Formula Hf(Formula c, Formula k, Formula e, Formula b) =>
        Call("fixedFiber", c, k, e, b);
    private static Formula Im(Formula c, Formula k) => Call("image", c, Call("pair", k, Num(1)));
    private static Formula Qcard => Card(V("A"));
    private static Formula Exponent => Subtract(Qcard, Num(1));
    private static Formula FixedLength(Formula c, Formula n) => All("w", Words,
        Imp(Mem(V("w"), c), Equal(Call("length", V("w")), n)));

    private static Formula FiniteCarriers(Formula c, Formula k) => And(
        Fin(c),
        All("j", V("Nat"), And(Fin(Call("pref", c, V("j"))), Fin(R(c, V("j"))),
            All("S", Languages, Imp(Mem(V("S"), R(c, V("j"))), Fin(V("S")))))),
        Fin(Q(c, k)), Fin(Im(c, k)),
        All("E", Languages, And(Fin(F(c, k, V("E"))),
            All("b", V("A"), Fin(Hf(c, k, V("E"), V("b")))))));

    private static Formula Identification(Formula c, Formula k)
    {
        var z = V("z"); var ez = Call("apply", V("e"), z);
        var val = Call("val", z); var eval = Call("val", ez);
        return Exists("e", Call("Equiv", Q(c, k), Im(c, k)), And(
            All("z", Q(c, k), Equal(eval,
                Call("pair", Call("fst", val), Call("singletonList", Call("snd", val))))),
            All("z", Q(c, k), Equal(Call("recut", eval), Call("forward", val))),
            All("z", Q(c, k), Equal(Call("snd", eval), Call("singletonList", Call("snd", val))))));
    }

    private static Formula Bounds(Formula c, Formula k, Formula basis, bool full)
    {
        var e = V("E"); var b = V("b"); var n = Card(R(c, k));
        var power = Pow(basis, Exponent);
        var total = full ? Multiply(Qcard, Pow(n, Qcard)) : Multiply(Multiply(Qcard, n), power);
        return And(All("E", Languages, Imp(Mem(e, R(c, k)), And(
            All("b", V("A"), Le(Card(Hf(c, k, e, b)), power)),
            Le(Card(F(c, k, e)), Multiply(Qcard, power))))), Le(Card(Q(c, k)), total));
    }

    private static Formula Attains(Formula nwidth, bool full)
    {
        var n = V("n"); var k = V("k"); var c = V("C");
        var e = V("E"); var b = V("b");
        var fullValue = V(full ? "true" : "false");
        var basis = full ? nwidth : Add(nwidth, Num(1));
        var power = Pow(basis, Exponent);
        var total = full ? Multiply(Qcard, Pow(nwidth, Qcard)) :
            Multiply(Multiply(Qcard, nwidth), power);
        return Exists("n", V("Nat"), Exists("k", V("Nat"), Exists("C", Languages, And(
            Call("Nonempty", c), FixedLength(c, n), Le(Num(1), k), Le(k, n),
            Imp(Equal(fullValue, V("true")), Call("FullBranching", c, k)),
            Equal(Card(R(c, k)), nwidth),
            All("E", Languages, Imp(Mem(e, R(c, k)), And(
                All("b", V("A"), Equal(Card(Hf(c, k, e, b)), power)),
                Equal(Card(F(c, k, e)), Multiply(Qcard, power))))),
            Equal(Card(Q(c, k)), total)))));
    }

    private static Formula Statement()
    {
        var n = V("n"); var c = V("C"); var k = V("k"); var z = V("z");
        var width = Card(R(c, k)); var prescribed = V("N");
        var universal = All("n", V("Nat"), All("C", Languages,
            Imp(FixedLength(c, n), Imp(Call("Nonempty", c), All("k", V("Nat"),
                Imp(Le(Num(1), k), Imp(Le(k, n), And(
                    FiniteCarriers(c, k), Lt(Num(0), width), Identification(c, k),
                    All("z", Pairs, Imp(Mem(z, Q(c, k)), Mem(Call("forward", z), R(c, k)))),
                    Bounds(c, k, Add(width, Num(1)), false),
                    Imp(Call("FullBranching", c, k), Bounds(c, k, width, true))))))))));
        var sharp = All("N", V("Nat"), Imp(Le(Num(1), prescribed),
            And(Attains(prescribed, false), Attains(prescribed, true))));
        return All("A", V("Type"), Seq(OpenBracket, Fin(V("A")), CloseBracket, Sp,
            Imp(Le(Num(2), Qcard), And(universal, sharp))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual predecessor is determined by its complete finite-alphabet derivative table.",
        H("Sharp finite-alphabet one recut"),
        Blocks(Describe.Lean(
            DescribeId.Create("sharp-finite-alphabet-one-recut"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/SharpFiniteAlphabetOneRecut.sharp_finite_alphabet_one_recut"),
            H("Actual carriers, sharp bounds, and simultaneous realization"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be any finite alphabet of cardinal q at least two. A language C is a nonempty set of words all of one length n. For every natural j, P_j=pref(C,j) is the set of length-j prefixes having a completion in C; R_j=residualSet(C,j) is the set of their actual residual languages R(v)={f: vf belongs to C}. At every cut 1 <= k <= n, let N=card(R_k). The theorem derives that C, every P_j and R_j, each residual in R_j, the one-credit boundary and all of its fibers are finite, and N is positive. It includes both k=1 and k=n.")),
                Paragraph(Text("For a residual S and letter b, derivative(S,b)={f: bf belongs to S}. The actual one-credit carrier oneBoundary(C,k) consists precisely of (S,b) with S in R_(k-1) and derivative(S,b) nonempty. forward(S,b)=derivative(S,b) always belongs to R_k on this carrier. The fixed fiber fixedFiber(C,k,E,b) is {S in R_(k-1): derivative(S,b)=E}; currentFiber(C,k,E) is {(S,b) in oneBoundary(C,k): forward(S,b)=E}. Thus the first cardinality is exactly h(E,b), without counting multiple prefixes that share a residual.")),
                Paragraph(Text("StrictIdentification gives an equivalence e from oneBoundary(C,k) onto the existing strict image(C,(k,1)). It sends (S,b) to (S,[b]); its forward residual is exactly the strict recut {f: [b]f belongs to S}, and its letter projection is the singleton tail [b]. This is an identification of actual images in both directions. In the displayed formula recut(S,t) denotes {f: tf belongs to S}. No independently chosen residual and tail are added to the carrier.")),
                Paragraph(Text("For each actual E in R_k and each b in A, h(E,b) <= (N+1)^(q-1), the whole forward fiber has cardinal at most q(N+1)^(q-1), and the entire one-credit carrier has cardinal at most qN(N+1)^(q-1). FullBranching(C,k) means that every actual extendable prefix v of length k-1 permits vb for every letter b. Under this condition the corresponding bounds are N^(q-1), qN^(q-1), and qN^q. The condition quantifies over all actual prefixes of the same C.")),
                Paragraph(Text("Since k-1<n, no actual preceding residual contains the empty word. Such a residual S is therefore recovered from the entire function b maps to derivative(S,b). Each entry is empty or an actual member of R_k, and every entry is actual under full branching. Fixing derivative(S,b)=E leaves the q-1 coordinates indexed by letters different from b. Restricting to these coordinates is injective on the fixed fiber. The same reconstruction gives injective finite encodings for the whole forward fiber and carrier. This proves the bounds without replacing the actual image by a presumed exhaustive table universe.")),
                Paragraph(Text("For simultaneous attainment fix any prescribed N>=1 over that same A. Choose an embedding of Bool into A. Transport the original optional-index word encoding word(i), for i in Option(Fin N), through this embedding. Denote the transported word by e(i); it has length N and is injective in i. Enumerate the finite alphabet once. For a table t:A to Option(Fin N), its anchor v(t) concatenates the q blocks e(t(a)) in this fixed order. Every anchor has length qN. Equal-length block cancellation and the original encoding injectivity recover each entry from its anchor.")),
                Paragraph(Text("A table is admissible in the unrestricted family when at least one coordinate is some s. In the full family every coordinate must be some s. Define the single literal language C in each regime to consist of exactly v(t)b e(some s), over all admissible t and all b,s satisfying t(b)=some s. Its length is qN+1+N, and its cut is qN+1. A positive N gives a constant table and an actual word, including when N=1. All blocks and all words lie in the original alphabet A; additional letters outside an embedded binary pair occur as selected letters and independent table coordinates.")),
                Paragraph(Text("The actual length-qN extendable prefixes are exactly the anchors v(t) of admissible tables. Their residuals are exactly S(t)={b e(some s): t(b)=some s}. Taking derivatives recovers the optional coordinate payloads, so t maps to S(t) injectively. The actual length-(qN+1) prefixes are exactly v(t)b with t(b)=some s; their residuals are the singleton languages {e(some s)}. Conversely every such table and selected coordinate has its stated literal completion. Thus there are exactly N current residuals and no extra preceding prefixes, residuals, or current prefixes.")),
                Paragraph(Text("The whole one-credit carrier is exactly {(S(t),b): t admissible and t(b)=some s for some s}. For a fixed actual singleton E={e(some s)} and a fixed letter b, all remaining coordinates are free: Option(Fin N) in the unrestricted family and the nonempty optional indices in the full family. Filling the selected coordinate with some s gives a bijection onto the actual fixed fiber. The fixed-fiber cardinalities are (N+1)^(q-1) and N^(q-1); summing over all q letters gives the current-fiber equalities. The same filling construction maps triples (s,b,r), with r the remaining-coordinate function, bijectively onto the entire actual one-credit carrier. Both directions use the exhaustive boundary classification. Injectivity recovers b, the full table, its selected index s and every remaining coordinate. Counting this whole-carrier bijection gives the total equalities. All three equalities therefore hold simultaneously in each one language. The complete preceding-prefix classification also proves full branching at every actual preceding prefix of the full family.")),
                Paragraph(Text("The attainment quantifiers are every finite A with q>=2, every positive N, every actual E, and every b in A. Each regime uses one language for all its equalities. Lengths and cuts may depend on A and N; attainment at each separately prescribed length and cut is outside this assertion. The full total qN times N^(q-1) equals qN^q because q is positive.")),
                Paragraph(Text("The strict supplied append and credit-limited deletion interpretation is the one of strict_anchored_specialization with d=1, the same C and the same k. Its legal-action equivalence and minimum exact boundary factor therefore apply through the explicit carrier equivalence. For the existing minimum_rollback_alphabet, use the actual finite source oneBoundary(C,k), first with the observation (forward,b) and then with forward alone. Its maximum fibers are respectively the maxima of h(E,b) and of card(currentFiber(C,k,E)); the theorem above computes their sharp values. This concerns the supplemental alphabet for exact recovery, rather than a total machine or physical memory cost.")),
                Paragraph(Text("The original binary one-recut result supplies the optional-index encoding and the literal-language precedent. The recursive right-language signature ingredient is described by Daciuk, Mihov, Watson and Watson, Incremental Construction of Minimal Acyclic Finite-State Automata, Computational Linguistics 26(1), section 2, pages 4-5. Radionova and Okhotin, A hierarchy of reversible finite automata, arXiv:2411.14538v1, Definition 2, supplies reversibility terminology. These sources are not attributed the finite-alphabet extremal constants proved here, and no worldwide priority claim is made."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ObserverMemory/SharpBinaryOneRecut")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ObserverMemory/StrictAnchoredBoundary"))]));
}
