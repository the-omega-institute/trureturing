using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class LegalResamplingSupportSignalDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional resampling on the complete positive-End legal source detects every effective support coordinate.",
        H("Uniform Support Signal on Legal Positive-End Words"),
        Blocks(
            Paragraph(Text("Input(n) is Fin(n) to the existing five-window alphabet "
                + "000,100,010,101,001, with bits written from low to high and positions starting at zero. "
                + "Positive(x) requires flattened-bit legality with initial bit false and a nonzero last window. "
                + "Every null window retains its position. The source is the finite set of these actual words.")),
            Paragraph(Text("The existing Roles(n) has p<q<r. The priority teacher returns 1 when "
                + "high(x(p)) and low(x(q)) hold, otherwise 2 when high(x(q)) and low(x(r)) hold, "
                + "and otherwise 0. Its support is the union of {p,q} when p+1<q and {q,r} when q+1<r. "
                + "This gives the four empty, first-edge, second-edge, and two-edge cases.")),
            Paragraph(Text("The completion fiber at I and x consists of positive legal words "
                + "that agree with x at each position outside I. It contains x whenever x belongs to the source. "
                + "signal(t,I) averages the indicator that the two teacher responses differ: first uniformly "
                + "over this nonempty completion fiber, then uniformly over the complete source. "
                + "Both averages are finite rational sums; coordinates within a word need not be independent.")),
            Describe.Lean(DescribeId.Create("legal-resampling-support-signal"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/LegalResamplingSupportSignal.result"),
                H("Disjoint support and a uniform lower bound"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bounds hold for every n at least four, every strict role "
                    + "triple and every set I of positions. Disjointness gives exact response equality. "
                    + "For a support position, neutral guards and the opposite endpoint can be fixed "
                    + "while retaining its original letter. Three original letters recover the preimage "
                    + "of this repair. Two available replacement letters give different responses "
                    + "in the same legal fiber. The squared-error decomposition of finite averages "
                    + "then transfers the singleton lower bound to any containing set."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = V("n");
        var t = V("t");
        var i = V("I");
        var overlap = Call("inter", i, Call("support", t));
        var empty = Seq(Par(overlap), Sp, Eq, Sp, Emptyset);
        var zero = Seq(Call("signal", t, i), Sp, Eq, Sp, D(0));
        var lower = Seq(Frac, Grp(D(2)), Grp(D(3,1,2,5)), Sp, Leq, Sp,
            Call("signal", t, i));
        var both = Seq(Par(Seq(empty, Sp, Implies, Sp, zero)), Sp, Land, Sp,
            Par(Seq(Call("Nonempty", overlap), Sp, Implies, Sp, lower)));
        return All(n, Seq(Mathbb, Grp(V("N"))),
            All(t, Call("Roles", n), All(i, Call("Finset", Call("Fin", n)),
                Seq(D(4), Sp, Leq, Sp, n, Sp, Implies, Sp, Par(both)))));
    }
}
