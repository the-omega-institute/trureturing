using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformResidualRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformResidualRealization", H("Uniform native residual realization"), Blocks(
            Entry("bounded_identity_reflection", "One tuple reflects a bounded syntax class", Bounded(),
                "MixedExpr uses arbitrary finite native grounds, decorated shared residual names and ordered pairs. Weight is the native constructor mass of a ground, zero on a decorated residual, and one plus the two child weights on a pair. Decoration is the largest fixed residual exponent. For weight bound M and decoration bound d, separator assigns name i the native iterate with exponent i times (d+1) of the existing comb of mass M+1. The unary operation is the interpreted native substitution, not a free constructor.",
                "A closed expression has mass at most its weight. A live expression at the separator has mass at least M+1; a live pair has mass at least M+2. Native mass remains invariant under every substitution power. These bounds distinguish closed from live terms and residuals from live pairs. The existing right-spine clock and the disjoint decoration intervals distinguish residual names and exponents. Actual ordered-pair injectivity then permits structural recursion. Closed equalities remain semantic native equalities; no equality of their expression syntax is claimed."),
            Entry("instantiate_eval", "Rank instantiation preserves native evaluation", Instantiation(),
                "For arbitrary dimensions k and m, an unbounded rank vector n, a native residual valuation z and a ranked expression E, evaluating the instantiated expression equals rankedEval n z E. Instantiation replaces each ranked leaf by the native iterate of alpha at its rank plus decoration; the residual leaves, arbitrary grounds and ordered pairs retain their original meanings.",
                "The ranked-leaf equality is the addition law for native substitution iterates. The pair case combines the two child equalities. Uniform residual reflection uses this transport at the separator and at every residual valuation. Finite prefix separation also uses it after binding fixed residual coordinates to grounds and the remaining coordinates to their original residual names."),
            Entry("uniform_residual_reflection", "The same tuple works at all atomic rank vectors", Uniform(false),
                "RankedExpr is the existing MixedExpr on Fin k plus Fin m. The left summand denotes the shared atom T at rank n(j); its residual decoration c denotes T at rank n(j)+c. The right summand denotes the original residual z(i), with its original fixed native power. Grounds remain arbitrary finite trees. Instantiation replaces only the ranked summand by actual native ground trees. Their masses are zero at every rank, so instantiation preserves the input weight without any bound on rank or native leaf count.",
                "ListWeight and listDecoration compute the maxima of both sides and all residual decorations. Every subexpression inherits the side bound because pairing increases weight. UniformSeparator is computed solely from this finite list and its residual dimension, before n is supplied. The list retains duplicates. The theorem quantifies over every unbounded shared rank vector and every listed pair. Empty lists, zero rank dimension, zero residual dimension, repeated names and unused names are all included."),
            Entry("simultaneous_completion", "Separate nonidentities admit one common completion", Uniform(true),
                "For each listed pair, a finite witness of disequality suffices. Uniform reflection makes the same precomputed tuple satisfy the entire finite conjunction. The witnesses in the premise may differ, whereas the conclusion uses exactly one tuple. NativeSimultaneousPrefixSeparation applies this consequence to the whole list after substituting independent prefix contexts. A joint finite witness therefore also gives this common completion, by taking that witness for each pair.",
                "These statements concern exact finite trees and whole-tree equalities. They imply no Presburger elimination, acquisition port, resource optimum, physical realization or full Functional Joint Contact theorem. No bounded-rank or common-clock promise is imposed.")
        )));
    private static DocumentBlock Entry(string n, string title, StatementSource statement, string first, string second) =>
        Describe.Lean(DescribeId.Create("native-uniform-" + n.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + n), H(title), statement,
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(first)), Paragraph(Text(second))), DescribeRole.Theorem);
    private static StatementSource Bounded()
    {
        var coord = Call("Fin", V("m"));
        var expr = Call("MixedExpr", coord);
        var sep = Call("separator", V("m"), V("M"), V("d"));
        var at = EqOf(Call("eval", sep, V("A")), Call("eval", sep, V("B")));
        var all = All("z", Arr(coord, V("Source")),
            EqOf(Call("eval", V("z"), V("A")), Call("eval", V("z"), V("B"))));
        return StatementSource.FromAuthor(Disp(All("m,M,d", V("Nat"), All("A,B", expr,
            Imp(LessEq(Call("weight", V("A")), V("M")),
            Imp(LessEq(Call("weight", V("B")), V("M")),
            Imp(LessEq(Call("decoration", V("A")), V("d")),
            Imp(LessEq(Call("decoration", V("B")), V("d")), IffOf(at, all)))))))));
    }
    private static StatementSource Instantiation()
    {
        var rank = Arr(Call("Fin", V("k")), V("Nat"));
        var tuple = Arr(Call("Fin", V("m")), V("Source"));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"), All("n", rank,
            All("z", tuple, All("E", Call("RankedExpr", V("k"), V("m")),
            EqOf(Call("eval", V("z"), Call("instantiate", V("n"), V("E"))),
                Call("rankedEval", V("n"), V("z"), V("E")))))))));
    }
    private static StatementSource Uniform(bool completion)
    {
        var expr = Call("RankedExpr", V("k"), V("m"));
        var pair = Call("Prod", expr, expr);
        var tuple = Arr(Call("Fin", V("m")), V("Source"));
        var sep = Call("uniformSeparator", V("L"));
        Formula Value(Formula z, string side) => Call("rankedEval", V("n"), z, Call(side, V("p")));
        Formula At(Formula z, bool neg) => neg ? NeOf(Value(z,"fst"),Value(z,"snd")) : EqOf(Value(z,"fst"),Value(z,"snd"));
        var conclusion = completion
            ? IffOf(All("p", pair, Imp(Mem(V("p"), V("L")), Some("z", tuple, At(V("z"),true)))),
                All("p", pair, Imp(Mem(V("p"), V("L")), At(sep,true))))
            : All("p", pair, Imp(Mem(V("p"), V("L")), IffOf(At(sep,false), All("z",tuple,At(V("z"),false)))));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"), All("L", Call("List",pair),
            All("n", Arr(Call("Fin",V("k")),V("Nat")), conclusion)))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula LessEq(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
