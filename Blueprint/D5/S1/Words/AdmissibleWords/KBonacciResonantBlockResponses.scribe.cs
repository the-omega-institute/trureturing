using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciResonantBlockResponsesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual original-order Boolean words have exact controlled block-response signatures.",
        H("Exact resonant block responses"),
        Blocks(
            Paragraph(Text(
                "Fix any order k at least two and block width m at least one. Set "
                + "T=k+1, g=gcd(m,T), and p=T/g, with g at least two. The actual "
                + "weight at position n is c_n=dbonacci k (n+2) modulo two. "
                + "A live record is (v,theta,s), where v lies in ZMod 2, theta lies "
                + "in the ambient ZMod T, and s is the length of the trailing run "
                + "of ones, below k. Complete block histories have theta in P, the "
                + "image of multiplication by g on ZMod T. Rejection is an "
                + "independent absorbing record and output.")),
            Paragraph(Text(
                "The original scanner increments s on a one when s+1 is below k, "
                + "rejects otherwise, and resets s to zero on a zero. Its acceptance "
                + "agrees with runAdmissible with maximum fuel k-1 and current fuel "
                + "k-1-s. Boolean lists and finite Boolean coordinate functions "
                + "describe the same words. DBonacciAdmissible is exactly acceptance "
                + "from zero. The source output of a legal word is the sum of its "
                + "true-bit weights c_i, and an illegal word outputs rejection.")),
            Paragraph(Text(
                "In the typed statement, natural subtraction is truncated and "
                + "natural division is floor division. A value annotated by a "
                + "ZMod type is the natural-number cast into that type; val is "
                + "the canonical natural representative. Triples associate to "
                + "the right. Finite-index brackets carry their displayed bound. "
                + "All sets, images, products, and cardinalities are finite. "
                + "FintypeDecidablePiFintype denotes the canonical finite "
                + "function equality decision Fintype.decidablePiFintype. "
                + "The Boolean parameter locally selects the full alphabet "
                + "when false and the locally legal alphabet when true.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-resonant-block-responses"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciResonantBlockResponses."
                    + "kbonacci_resonant_block_responses"),
                H("Signatures, joint reachability, and exact response classes"),
                StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural horizon H, put b=mH. W_j(theta) is the "
                        + "vector of actual weights c_(theta.val+i) for i in Fin j. "
                        + "At H=0 the signature is the current value, with a separate "
                        + "rejection symbol. At positive H, a nonterminal tail s<k-1 "
                        + "has signature (v,min(k-s,b+1),W_b(theta)). A terminal "
                        + "tail s=k-1 has the separate terminal tag and signature "
                        + "(v,terminal,W_(b-1)(theta+1)). The terminal tag is distinct "
                        + "from every numeric threshold.")),
                    Paragraph(Text(
                        "For each input alphabet, two records have the same signature "
                        + "if and only if their output functions agree on every "
                        + "controlled suffix of at most H complete blocks. The full "
                        + "alphabet contains all m-bit words. The local alphabet "
                        + "contains precisely those m-bit words accepted from zero. "
                        + "Local legality is tested separately in each aligned block; "
                        + "it permits rejection when a run of k ones crosses a block "
                        + "boundary. Only outputs at complete block endpoints and the "
                        + "current endpoint are observed.")),
                    Paragraph(Text(
                        "The actual weights have period k+1 modulo two. A one-bit "
                        + "transition adds c_theta to v on a surviving one, advances "
                        + "the ambient phase by one, and increments the tail. A zero "
                        + "advances the phase and clears the tail while keeping v. "
                        + "Concatenation composes these transitions exactly, so an "
                        + "m-bit block is m successive actual one-bit updates. No "
                        + "restriction to P is imposed at intermediate bit positions.")),
                    Paragraph(Text(
                        "Every v, every phase in P, and every tail below k are jointly "
                        + "realized by one legal word of length divisible by m, in "
                        + "both input alphabets. Compatible congruences select a "
                        + "sufficiently large length N, divisible by m and congruent "
                        + "to theta modulo k+1. An optional initial pulse, zeros, "
                        + "and s final ones produce the requested value, phase, "
                        + "and tail together, because c_0=1. The record set is "
                        + "exactly the actual source image. From every record a "
                        + "finite suffix of locally legal blocks reaches rejection: "
                        + "zeros first clear the tail, k-1 ones end at a block "
                        + "boundary, and a one in the next block rejects.")),
                    Paragraph(Text(
                        "Equal nonterminal signatures determine both the weighted "
                        + "increments and the initial-run rejection threshold for "
                        + "every suffix. After a first zero, the scanner has a common "
                        + "tail. For terminal records a first one rejects, whereas a "
                        + "first zero clears the tail and exposes exactly b-1 "
                        + "remaining weights from theta+1, including phase wrap. "
                        + "Conversely, the empty suffix distinguishes current "
                        + "values, padded initial runs distinguish unequal thresholds, "
                        + "and isolated pulses distinguish unequal window coordinates. "
                        + "A pulse in the first position separates the terminal and "
                        + "nonterminal tags. Terminal window pulses have an initial "
                        + "zero. Each distinguishing word belongs to both alphabets; "
                        + "an initial-run word may use the entire budget without "
                        + "a trailing zero.")),
                    Paragraph(Text(
                        "For positive H, there are min(b,k-1) nonterminal thresholds, "
                        + "min(p,b/g+2) "
                        + "nonterminal windows, and min(p,b/g+1) terminal windows. "
                        + "Every combination with either current value is realized "
                        + "by the same-source construction. The disjoint terminal "
                        + "and nonterminal families, together with one rejection "
                        + "class, give the displayed exact counts. The conclusions "
                        + "include k=2, p=1, g=2, H=0, and arbitrarily long horizons.")),
                    Paragraph(Text(
                        "Zero padding preserves the final output and absorbing "
                        + "rejection. Nonempty padding increases length, advances "
                        + "phase, and resets the live tail; empty padding leaves "
                        + "the record unchanged. Thus the equality relations on "
                        + "controlled response "
                        + "functions for at most H blocks and exactly H blocks "
                        + "coincide, for final outputs and for complete endpoint "
                        + "trajectories, including the current endpoint and H=0. "
                        + "The comparison quantifies over every allowed suffix. "
                        + "It does not assert that one final observed value recovers "
                        + "the earlier trajectory of an already executed input."))),
                DescribeRole.Theorem))));
    private static Formula MainFormula()
    {
        var k = F.Id("k"); var m = F.Id("m"); var T = F.Id("T");
        var g = F.Id("g"); var p = F.Id("p"); var z = F.Id("z");
        var K = F.Id("K"); var Z = F.Id("Z"); var S = F.Id("S");
        var Q = F.Id("Q"); var R = F.Id("R"); var B = F.Id("B");
        var P = F.Id("P"); var n = F.Id("n"); var j = F.Id("j");
        var i = F.Id("i"); var H = F.Id("H"); var w = F.Id("w");
        var s = F.Id("s"); var v = F.Id("v"); var theta = Theta;
        var r = F.Id("r"); var q = F.Id("q"); var x = F.Id("x");
        var y = F.Id("y"); var u = F.Id("u"); var h = F.Id("h");
        var locally = F.Id("locally"); var a = F.Id("a"); var d = F.Id("d");
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var boolean = Op("Bool");
        var prop = Op("Prop");
        var none = Op("none"); var yes = Op("true"); var no = Op("false");
        var zero = D(0); var one = D(1); var two = D(2);
        var b = Multiply(m, H);
        var next = Add(Call("val", s), one);
        var safe = Rel(next, Lt, k);
        var live = Call("some", Tuple(v, theta, s));
        var indexed = Call("ofFn", w);
        var wordType = Arrow(Call("Fin", n), boolean);
        var vectors = Arrow(Call("Fin", j), K);
        var signatureType = Call("Option", ProductType(K,
            Call("Sum", ProductType(nat, Arrow(Call("Fin", b), K)),
                Arrow(Call("Fin", Subtract(b, one)), K))));
        var qValue = Call("fst", q);
        var qPhase = Call("fst", Call("snd", q));
        var qTail = Call("snd", Call("snd", q));
        var sourceRecord = Call("source", w);
        var responseEquality = Equal(Call("response", x, w), Call("response", y, w));
        var endpointEquality = Equal(Call("response", x, Call("take", Multiply(j, m), w)),
            Call("response", y, Call("take", Multiply(j, m), w)));
        var definitions = Rows(
            Equal(T, Add(k, one)), Equal(g, Call("gcd", m, T)),
            Equal(p, Call("div", T, g)),
            Equal(K, Call("ZMod", two)), Equal(Z, Call("ZMod", T)),
            Equal(S, Call("Fin", k)),
            Equal(Q, ProductType(K, ProductType(Z, S))),
            Equal(R, Call("Option", Q)), Equal(B, Call("List", boolean)),
            Seq(Op("letI"), Sp, As(d, All(j, nat, Call("DecidableEq", vectors))), Eq,
                Lam(j, nat, Lam(Seq(a, Comma, w), vectors,
                    Call("FintypeDecidablePiFintype", a, w)))),
            Equal(z, As(zero, S)),
            Equal(As(Op("base"), Call("PartialDFA", boolean, S)),
                Seq(Open, Op("start"), Eq, z, Comma, Op("step"), Eq,
                    Lam(s, S, Lam(x, boolean,
                        If(Equal(x, yes), DepIf(h, safe,
                            Call("some", FinIndex(next, h, S)), none), Call("some", z)))), Close)),
            Equal(As(Op("run"), Arrow(S, Arrow(B, Call("Option", S)))),
                Call("evalFrom", Op("base"))),
            Equal(As(Op("c"), Arrow(nat, K)),
                Lam(n, nat, As(Call("dbonacci", k, Add(n, two)), K))),
            Equal(As(P, Call("Finset", Z)),
                Call("image", Lam(theta, Z, Multiply(As(g, Z), theta)), Call("univ", Z))),
            Equal(Op("W"), Lam(j, nat, Lam(theta, Z,
                Lam(i, Call("Fin", j), Call("c", Add(Call("val", theta), Call("val", i))))))),
            Equal(As(Op("addValue"), Arrow(Z, Arrow(B, K))),
                Lam(theta, Z, Lam(w, B,
                    SumOver(i, Call("Fin", Call("length", w)),
                        If(Equal(Call("get", w, i), yes),
                            Call("c", Add(Call("val", theta), Call("val", i))), zero))))),
            Equal(As(Op("advance"), Arrow(R, Arrow(B, R))),
                Lam(r, R, Lam(w, B,
                    Call("bind", r, Lam(q, Q,
                        Call("map", Lam(s, S,
                            Tuple(Add(qValue, Call("addValue", qPhase, w)),
                                Add(qPhase, As(Call("length", w), Z)), s)),
                            Call("run", qTail, w))))))),
            Equal(As(Op("output"), Arrow(R, Call("Option", K))),
                Lam(r, R, Call("map", Lam(q, Q, qValue), r))),
            Equal(As(Op("response"), Arrow(R, Arrow(B, Call("Option", K)))),
                Lam(r, R, Lam(w, B, Call("output", Call("advance", r, w))))),
            Equal(As(Op("source"), Arrow(B, R)),
                Lam(w, B, Call("advance", Call("some", Tuple(As(zero, K), As(zero, Z), z)), w))),
            Equal(As(Op("blocks"), Arrow(boolean, Arrow(B, prop))),
                Lam(locally, boolean, Lam(w, B, And(
                    Rel(m, Mid, Call("length", w)),
                    Imp(Equal(locally, yes), All(j, nat,
                        Imp(Rel(Multiply(j, m), Lt, Call("length", w)),
                            NotEqual(Call("run", z,
                                Call("take", m, Call("drop", Multiply(j, m), w))), none)))))))),
            Equal(As(Op("records"), Call("Finset", R)),
                Call("insert", none, Call("image", Lam(q, Q, Call("some", q)),
                    Call("product", Call("univ", K), Call("product", P, Call("univ", S)))))),
            Equal(Op("signature"), Lam(H, nat, Lam(r, R,
                Call("map", Lam(q, Q, Tuple(qValue,
                    If(Equal(H, zero),
                        Call("inl", Tuple(zero, Call("W", b, qPhase))),
                        If(Equal(Call("val", qTail), Subtract(k, one)),
                            Call("inr", Call("W", Subtract(b, one), Add(qPhase, one))),
                            Call("inl", Tuple(Call("min", Subtract(k, Call("val", qTail)), Add(b, one)),
                                Call("W", b, qPhase))))))), r)))),
            Equal(Op("Sig"), Lam(H, nat, signatureType)),
            As(Op("signature"), All(H, nat, Arrow(R, Call("Sig", H)))),
            Equal(Op("atMost"), Lam(H, nat, Lam(locally, boolean, Lam(Seq(x, Comma, y), R,
                All(w, B, Imp(Call("blocks", locally, w),
                    Imp(Rel(Call("length", w), Leq, b), responseEquality))))))),
            Equal(Op("exactFinal"), Lam(H, nat, Lam(locally, boolean, Lam(Seq(x, Comma, y), R,
                All(w, B, Imp(Call("blocks", locally, w),
                    Imp(Equal(Call("length", w), b), responseEquality))))))),
            Equal(Op("atMostTrajectory"), Lam(H, nat, Lam(locally, boolean, Lam(Seq(x, Comma, y), R,
                All(w, B, Imp(Call("blocks", locally, w),
                    Imp(Rel(Call("length", w), Leq, b), All(j, nat,
                        Imp(Rel(Multiply(j, m), Leq, Call("length", w)), endpointEquality))))))))),
            Equal(Op("exactTrajectory"), Lam(H, nat, Lam(locally, boolean, Lam(Seq(x, Comma, y), R,
                All(w, B, Imp(Call("blocks", locally, w),
                    Imp(Equal(Call("length", w), b), All(j, nat,
                        Imp(Rel(Multiply(j, m), Leq, Call("length", w)), endpointEquality))))))))),
            Equal(Op("C"), Lam(H, nat,
                Call("card", Call("image", Lam(r, R, Call("signature", H, r)), Op("records"))))));
        var clauses = ConjoinedRows(
            All(n, nat, All(w, wordType, All(s, S,
                Equal(Call("isSome", Call("run", s, indexed)),
                    Call("runAdmissible", Subtract(k, one),
                        Subtract(Subtract(k, one), Call("val", s)), n, w))))),
            All(n, nat, All(w, wordType,
                Rel(Call("DBonacciAdmissible", k, n, w), Iff,
                    NotEqual(Call("source", indexed), none)))),
            All(n, nat, All(w, wordType,
                Equal(Call("output", Call("source", indexed)),
                    If(Call("DBonacciAdmissible", k, n, w),
                        Call("some", SumOver(i, Call("Fin", n),
                            If(Equal(App(w, i), yes),
                                As(Call("dbonacci", k, Add(Call("val", i), two)), K), zero))), none)))),
            All(w, B, All(v, K, All(theta, Z, All(s, S,
                Imp(Equal(sourceRecord, live), And(
                    Equal(theta, As(Call("length", w), Z)),
                    Equal(Call("val", s), Call("length", Call("takeWhile", Op("id"), Call("reverse", w)))))))))),
            All(theta, Z, All(n, nat,
                Equal(Call("c", Add(Call("val", theta), n)),
                    Call("c", Call("val", Add(theta, As(n, Z))))))),
            All(v, K, All(theta, Z, All(s, S, All(x, boolean,
                Equal(Call("advance", live, Seq(OpenBracket, x, CloseBracket)),
                    If(Equal(x, yes), DepIf(h, safe,
                        Call("some", Tuple(Add(v, Call("c", Call("val", theta))),
                            Add(theta, one), FinIndex(next, h, S))), none),
                        Call("some", Tuple(v, Add(theta, one), z)))))))),
            All(r, R, All(Seq(u, Comma, v), B,
                Equal(Call("advance", r, Append(u, v)),
                    Call("advance", Call("advance", r, u), v)))),
            All(w, B, Equal(Call("response", none, w), none)),
            All(locally, boolean, All(r, R,
                Rel(Rel(r, InMacro, Op("records")), Iff,
                    Ex(w, B, And(Call("blocks", locally, w), Equal(sourceRecord, r)))))),
            All(locally, boolean, All(r, R, Ex(w, B,
                And(Call("blocks", locally, w), Equal(Call("advance", r, w), none))))),
            All(H, nat, All(locally, boolean, All(Seq(x, Comma, y), R,
                Rel(Call("atMost", H, locally, x, y), Iff,
                    Equal(Call("signature", H, x), Call("signature", H, y)))))),
            All(H, nat, All(locally, boolean, All(Seq(x, Comma, y), R, And(
                Par(Rel(Call("atMost", H, locally, x, y), Iff, Call("exactFinal", H, locally, x, y))),
                Par(Rel(Call("atMost", H, locally, x, y), Iff, Call("atMostTrajectory", H, locally, x, y))),
                Par(Rel(Call("atMost", H, locally, x, y), Iff, Call("exactTrajectory", H, locally, x, y))))))),
            Equal(Call("C", zero), D(3)),
            All(H, nat, Imp(Rel(one, Leq, H),
                Equal(Call("C", H), Add(one, Multiply(two,
                    Add(Multiply(Call("min", b, Subtract(k, one)),
                        Call("min", p, Add(Call("div", b, g), two))),
                        Call("min", p, Add(Call("div", b, g), one)))))))));
        return All(Seq(k, Comma, m), nat,
            Imp(And(Rel(two, Leq, k), Rel(one, Leq, m),
                Rel(two, Leq, Call("gcd", m, Add(k, one)))),
                Seq(Op("let"), Sp, definitions, Sp, Op("in"), Sp, clauses)));
    }

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula As(Formula value, Formula type) => Par(Seq(value, Colon, type));
    private static Formula Rel(Formula left, Formula relation, Formula right) => Seq(left, Sp, relation, Sp, right);
    private static Formula Arrow(Formula domain, Formula codomain) => Rel(domain, To, codomain);
    private static Formula ProductType(Formula left, Formula right) => Rel(left, Times, Par(right));
    private static Formula Tuple(params Formula[] items) => Par(Join(items, Comma));
    private static Formula Append(Formula left, Formula right) => Seq(left, Plus, Plus, right);
    private static Formula All(Formula variables, Formula type, Formula body) => Bound(Forall, variables, type, body);
    private static Formula Ex(Formula variables, Formula type, Formula body) => Bound(Exists, variables, type, body);
    private static Formula Lam(Formula variables, Formula type, Formula body) => Bound(LambdaLower, variables, type, body);
    private static Formula Bound(Formula binder, Formula variables, Formula type, Formula body) =>
        Par(Seq(binder, Sp, Open, variables, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Imp(Formula premise, Formula body) => Par(Rel(Par(premise), Implies, Par(body)));
    private static Formula If(Formula condition, Formula yes, Formula no) => Cases(
        Seq(yes, Amp, condition), Seq(no, Amp, Op("otherwise")));
    private static Formula DepIf(Formula witness, Formula condition, Formula yes, Formula no) => Cases(
        Seq(yes, Amp, Op("if"), Sp, witness, Colon, condition), Seq(no, Amp, Op("otherwise")));
    private static Formula FinIndex(Formula value, Formula bound, Formula type) =>
        As(Seq(Langle, Sp, value, Comma, bound, Rangle), type);
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, domain), Sp, Par(body));
    private static Formula Cases(params Formula[] rows) =>
        Seq(Begin, Grp(F.Id("cases")), Join(rows, RowBreak), End, Grp(F.Id("cases")));
    private static Formula Rows(params Formula[] rows) => new Formula.Aligned([.. rows]);
    private static Formula And(params Formula[] clauses) => Par(Join(clauses, Seq(Sp, Land, Sp)));
    private static Formula ConjoinedRows(params Formula[] clauses) => Rows(Join(clauses, Seq(RowBreak, Sp, Land, Sp)));
    private static Formula Join(Formula[] items, Formula separator)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var index = 0; index < items.Length; index++)
        {
            if (index > 0) result.Add(separator);
            result.Add(items[index]);
        }
        return Seq([.. result]);
    }
}
