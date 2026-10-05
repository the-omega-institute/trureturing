using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawEntersTriangleDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Fn(string s, params Formula[] args) => Call(s, args);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula And(Formula a, Formula b) =>
        Seq(Open, a, Sp, Land, Sp, b, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical triangular paths for all positive attaining laws.",
        H("Optimal Laws Enter the Triangular Graph"), Blocks(
            Describe.Lean(DescribeId.Create("optimal-law-path"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawEntersTriangle.result"),
                H("Fixed relabelling and exact cost"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let m >= 2 and let p be a strictly positive real probability "
                        + "law on m labels. Suppose its dyadic cost equals alpha(m) times its "
                        + "minimum coordinate. Then there is a fixed permutation sigma and a "
                        + "legal reduced triangular root path gamma whose written probabilities "
                        + "are p(sigma(i)). Its anchor mass is the minimum of p, and its layer "
                        + "cost is exactly the dyadic cost of p.")),
                    Paragraph(Text("Each coordinate above the minimum has a least terminating "
                        + "binary depth D and equals the nearest strictly larger grid point "
                        + "at that depth. Its floor prefixes agree with the anchor at every "
                        + "shallower depth: an earlier disagreement would place the coordinate "
                        + "on an earlier binary grid, contrary to minimality. At and after D its "
                        + "fractional tail is zero. Thus a label outside the equal-prefix group "
                        + "writes no further digits.")),
                    Paragraph(Text("Sort the coordinates in increasing order. At every depth "
                        + "the equal-prefix group is an initial label interval. Its fractional "
                        + "tails sum to the integer residual r, and each tail is below one, "
                        + "so r < e. An anchor one forces all e retained labels to write one. "
                        + "An anchor zero permits only terminal departures, each with current "
                        + "tail one half; the anchor tail is strictly below one half. Hence "
                        + "the two cases satisfy e <= 2r and 2r < e respectively. The labels "
                        + "departing together occupy the end of the current interval, and the "
                        + "residual recurrence gives the two triangular successors.")),
                    Paragraph(Text("The written digits coincide with the coordinates' canonical "
                        + "binary digits. The original carry embedding supplies the integer "
                        + "residuals and anchor expansion, so both infinite series retain "
                        + "their exact values. No rationality or computability assumption is "
                        + "imposed on the positive real law."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m = V("m"); var p = V("p"); var i = V("i");
        var sigma = V("sigma"); var gamma = V("gamma");
        var indices = Fn("Fin", m); var real = Seq(Mathbb, Grp(V("R")));
        var positive = All(i, indices, Seq(D(0), Sp, Lt, Sp, Fn("p", i)));
        var normalized = Equal(Seq(new Formula.Subscript(Sum, i), Fn("p", i)), D(1));
        var optimal = Equal(Fn("L", p), Seq(Fn("alpha", m), Cdot, Fn("min", p)));
        var law = All(i, indices, Equal(Fn("probability", gamma, i), Fn("p", Fn("sigma", i))));
        var anchor = Equal(Fn("anchorMass", gamma), Fn("min", p));
        var cost = Equal(Fn("pathCost", gamma), Fn("L", p));
        var exists = Seq(Open, Exists, Sp, sigma, Colon, Sp, Fn("Perm", indices), Comma, Sp,
            Exists, Sp, gamma, Colon, Sp, Fn("RootPath", m), Comma, Sp,
            And(law, And(anchor, cost)), Close);
        return Disp(All(m, Seq(Mathbb, Grp(V("N"))), Seq(Open, m, Sp, Ge, Sp, D(2), Sp,
            Implies, Sp, All(p, Seq(indices, Sp, To, Sp, real),
                Seq(Open, And(positive, And(normalized, optimal)), Sp, Implies, Sp, exists, Close)), Close)));
    }
}
