using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class CompleteFailureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole polynomial targets, actual response intersections and failure against arbitrary deterministic policies with early stopping.",
        H("Complete targets and literal failure"),
        Blocks(
            Paragraph(Text("A world of degree bound d stores a strictly entrywise positive real 2 by 2 source of rank one and trace one, a nonzero vector of d+1 ordinary polynomial coefficients, and an arbitrary real constant drift. Its gain is the whole polynomial of those coefficients. Boolean false denotes M=[[0,1],[1,1]], and true denotes J=[[0,1],[1,0]]. A finite list v is chronological: appending an atom left-multiplies the cumulative matrix. At original clock i, readAt(W,v,i) evaluates the same whole gain at i and multiplies it by the trace of the cumulative matrix of take(v,i) against the fixed source, then adds the drift. The initial read is included. There are no other observation ports or unobserved compound actions.")),
            Describe.Lean(DescribeId.Create("positive-singular-source-rank"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompleteFailure.legal_source_iff"),
                H("The original singular-source condition"),
                StatementSource.FromAuthor(SourceStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In dimension two, positivity, zero determinant and trace one are exactly the existing legal-source condition. For the reverse direction the source is written in the positive chart with parameters P(1,0)/P(0,0) and P(0,1)/P(0,0). Its determinant equation and trace normalization give the exact original matrix. Thus no symmetry or off-diagonal equality is added."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("whole-polynomial-domain"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompleteFailure.whole_domain"),
                H("Exact unrestricted complete-domain correspondence"),
                StatementSource.FromAuthor(DomainStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero real polynomial of degree at most d is represented by its first d+1 coefficients, and reconstruction returns that same polynomial. Conversely, the ordinary polynomial of a world's coefficient vector is nonzero and has the stated degree bound. The source and drift are unchanged in both directions. Gain signs, lower degrees, all sampled or repeated roots and all real constant drifts remain present."))), DescribeRole.Theorem),
            Paragraph(Text("For a word v and an initial-inclusive reading vector h, wholeSet(v,h) consists of all worlds with readings(W,v)=h. There is no additional source or gain promise. The actual child slice(K,v,E,z) contains precisely those W in K whose immediate reading after the single next atom E is z. When K is compatible with one literal history, these are exactly its intersections with the corresponding complete child fibers.")),
            Paragraph(Text("Write N(K) for the existence of two distinct members of K. The failure recursion is L(0,K,v)=N(K), and L(n+1,K,v)=N(K) together with: for each Boolean atom E there exists a real response z with L(n,slice(K,v,E,z),v++[E]). Both action clauses are required. The repeated guard prevents a correct complete-target early stop at every node, including the terminal nodes.")),
            Describe.Lean(DescribeId.Create("same-history-inclusion"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompleteFailure.loses_mono"),
                H("Same-history inclusion monotonicity"),
                StatementSource.FromAuthor(MonoStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction preserves the distinct pair and sends each losing child into the corresponding full response intersection of the larger set. No cardinality or finiteness assumption is imposed on either set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-native-recursion-equivalence"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompleteFailure.finite_losing_iff"),
                H("Agreement with finite native-world failure"),
                StatementSource.FromAuthor(FiniteStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For cubic worlds and any finite support T, the set recursion is equivalent to MixedTripleExclusion.Losing. Set nontriviality is exactly cardinality at least two, and every child is the same full filter of the current support. The equivalence follows by induction on the remaining horizon."))), DescribeRole.Theorem),
            Paragraph(Text("A policy P receives the entire actual reading vector on each literal word and returns either a next Boolean atom or a complete world. Its choice can be an arbitrary deterministic function of that history. Identifies(P,0,v,W) means it returns W immediately. For n+1 further readings a returned world must equal W, while a chosen atom is immediately read on W and the policy continues at the extended literal word with n reads left. This semantics allows every early stop and imposes no output palette.")),
            Describe.Lean(DescribeId.Create("failure-excludes-early-stopping-policies"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CompleteFailure.loses_excludes_policy"),
                H("Every losing fiber defeats every policy"),
                StatementSource.FromAuthor(PolicyStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All candidates start at the same literal history h. If the policy stops, the guard supplies two distinct complete targets receiving the same output. If it chooses an atom, the failure recursion supplies a losing actual child. Equality of the old full histories and of the new response gives equality of the new full histories; the induction hypothesis then applies. Thus the result concerns acquired original-clock histories and complete targets throughout."))), DescribeRole.Theorem))));

    private static Formula I(string n) => F.Id(n);
    private static Formula C(string n, Formula x) => Seq(Operatorname, Grp(I(n)), Open, x, Close);
    private static Formula R => Seq(Mathbb, Grp(I("R")));
    private static Formula A => Seq(R, Caret, Grp(Seq(D(2), Times, D(2))));
    private static Formula All(Formula x, Formula body) => Seq(Forall, Sp, x, Comma, Sp, body);
    private static Formula L(Formula n, Formula k, Formula v) => C("L", Seq(n, Comma, k, Comma, v));
    private static Formula SourceBody(Formula p) => Seq(
        Open, Forall, Sp, I("i"), Comma, I("j"), InMacro, Sp,
        OpenBrace, D(0), Comma, D(1), CloseBrace, Comma, Sp,
        D(0), Lt, Sp, C("entry", Seq(p, Comma, I("i"), Comma, I("j"))), Close,
        Land, Sp, C("det", p), Eq, Sp, D(0), Land, Sp, C("tr", p), Eq, Sp, D(1));
    private static Formula SourceStatement() => Disp(All(Seq(I("P"), InMacro, Sp, A),
        Seq(C("LegalSource", I("P")), Iff, Sp, SourceBody(I("P")))));
    private static Formula DomainStatement()
    {
        var p = I("P"); var f = I("p"); var w = I("W"); var d = I("d"); var drift = I("z");
        return Disp(All(Seq(d, InMacro, Sp, Mathbb, Grp(I("N"))),
            All(Seq(p, InMacro, Sp, A), All(Seq(f, InMacro, Sp, C("Polynomial", R)),
            All(Seq(drift, InMacro, Sp, R), Seq(
                Open, Exists, Sp, w, InMacro, Sp, C("World", d), Comma, Sp,
                C("source", w), Eq, Sp, p, Land, Sp, C("gain", w), Eq, Sp, f,
                Land, Sp, C("drift", w), Eq, Sp, drift, Close, Iff, Sp,
                SourceBody(p), Land, Sp, f, Neq, Sp, D(0), Land, Sp,
                C("natDegree", f), Leq, Sp, d))))));
    }
    private static Formula Nat => Seq(Mathbb, Grp(I("N")));
    private static Formula Word => C("List", I("Bool"));
    private static Formula Bind(string x, Formula t, Formula body) =>
        All(Seq(I(x), InMacro, Sp, t), body);
    private static Formula Worlds => C("World", I("d"));
    private static Formula MonoStatement()
    {
        var body = Seq(L(I("n"), I("K"), I("v")), Land, Sp,
            I("K"), Subseteq, Sp, I("S"), Implies, Sp, L(I("n"), I("S"), I("v")));
        body = Bind("v", Word, body);
        body = Bind("S", C("Set", Worlds), body);
        body = Bind("K", C("Set", Worlds), body);
        body = Bind("n", Nat, body);
        return Disp(Bind("d", Nat, body));
    }
    private static Formula FiniteStatement()
    {
        var body = Seq(L(I("n"), C("coe", I("T")), I("v")), Iff, Sp,
            C("FiniteLosing", Seq(I("n"), Comma, I("T"), Comma, I("v"))));
        body = Bind("v", Word, body);
        body = Bind("T", C("Finset", C("World", D(3))), body);
        return Disp(Bind("n", Nat, body));
    }
    private static Formula PolicyStatement()
    {
        var body = Seq(I("K"), Subseteq, Sp, C("wholeSet", Seq(I("v"), Comma, I("h"))),
            Land, Sp, L(I("n"), I("K"), I("v")), Implies, Sp, Neg, Sp,
            Open, Forall, Sp, I("W"), InMacro, Sp, I("K"), Comma, Sp,
            C("Identifies", Seq(I("P"), Comma, I("n"), Comma, I("v"), Comma, I("W"))), Close);
        body = Bind("P", C("Policy", I("d")), body);
        body = Bind("h", C("History", I("v")), body);
        body = Bind("v", Word, body);
        body = Bind("K", C("Set", Worlds), body);
        body = Bind("n", Nat, body);
        return Disp(Bind("d", Nat, body));
    }
}
