using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class TwoPointGridDominanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive actual corners control the sum of squared distances to two coordinate grids.",
        H("Actual corners and the distance variance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-point-grid-distance-domain"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_point_grid_domain"),
                H("The positive envelope domain"),
                StatementSource.FromAuthor(DomainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c and d assign real endpoints to Fin 2, with 0 < c(i) < d(i) for each coordinate. Let A and B be real budgets. The set C consists of actual endpoint pairs whose coordinate sum lies in the closed interval from A to B. Write V for the sum of the two squared distances from the interval [A/2,B/2] to the coordinate sets. The distance to a two point set is the minimum of the distances to its two points.")),
                    Paragraph(Math(Disp(Seq(
                        F.Id("C"), Sp, Eq, Sp, Call("corners", C, Dd, A, B), Comma, Sp,
                        V, Sp, Eq, Sp, Call("varianceFloor", C, Dd, A, B))))),
                    Paragraph(Text(
                        "A single positive actual corner suffices: B/2 is positive and V lies between zero and 2(B/2) squared, with a strict upper inequality. The quantity V is a sum of squared deviations, not an average. Neither a positive lower budget nor a strict budget width is assumed here.")),
                    Paragraph(Text(
                        "For an actual corner (x,y), its mean m=(x+y)/2 belongs to [A/2,B/2]. Each set distance is at most the absolute deviation of the corresponding coordinate from m. Their squared sum is at most (x-m) squared plus (y-m) squared, which equals 2m squared minus 2xy. Positivity of xy makes this strictly smaller than 2m squared, and m is at most B/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-actual-corners-lower-endpoint"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominance.two_actual_corners_lower_mem"),
                H("The lower corner of a straddling row"),
                StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c,d,t,u,A,B be arbitrary real numbers. Define S to be the endpoint pairs in {c,d} times {t,u} whose sum lies in [A,B]. Nontrivial means that S contains two different pairs; their sums may be equal.")),
                    Paragraph(Math(Disp(RowSetFormula()))),
                    Paragraph(Text(
                        "If c+t < B < d+t, then A is at most c+t and c+t is at most B. Thus the lower corner (c,t) belongs to the slab. No positivity or ordering of the second pair of endpoints is required.")),
                    Paragraph(Text(
                        "Suppose instead that c+t < A. The pairs (c,t) and (d,t) are outside the slab. If both remaining pairs (c,u) and (d,u) belonged to it, comparing their lower and upper sum inequalities with the two strict inequalities would give a contradiction. Consequently at most one pair could belong to S, contradicting the two different pairs."))),
                DescribeRole.Theorem))));

    private static Formula C => F.Id("c");
    private static Formula Dd => F.Id("d");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula V => F.Id("V");
    private static Formula Square(Formula x) => Seq(Open, x, Close, Caret, Grp(D(2)));
    private static Formula RealQuantifier(params Formula[] variables) => Seq(
        Forall, Sp, Seq(variables), Colon, Sp, Call("Real"), Comma, Sp);

    private static Formula DomainFormula() => Disp(Seq(
        Forall, Sp, C, Comma, Dd, Colon, Sp, Call("Fin", D(2)), Sp, To, Sp,
        Call("Real"), Comma, Sp, RealQuantifier(A, Comma, B), Open,
        Open, Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
        D(0), Sp, Lt, Sp, Call("c", F.Id("i")), Sp, Land, Sp,
        Call("c", F.Id("i")), Sp, Lt, Sp, Call("d", F.Id("i")), Close,
        Sp, Land, Sp, Call("Nonempty", Call("corners", C, Dd, A, B)), Close,
        Sp, Implies, Sp, Open,
        D(0), Sp, Lt, Sp, Seq(Frac, Grp(B), Grp(D(2))), Sp, Land, Sp,
        D(0), Sp, Le, Sp, Call("varianceFloor", C, Dd, A, B), Sp, Land, Sp,
        Call("varianceFloor", C, Dd, A, B), Sp, Lt, Sp, D(2), Square(Seq(Frac, Grp(B), Grp(D(2)))), Close));

    private static Formula RowSetFormula() => Seq(
        F.Id("S"), Sp, Eq, Sp, OpenBrace, Sp, Open, F.Id("x"), Comma, F.Id("y"), Close,
        Sp, InMacro, Sp, Call("Real"), Caret, Grp(D(2)), Sp, Mid, Sp,
        Open, F.Id("x"), Sp, Eq, Sp, C, Sp, Lor, Sp, F.Id("x"), Sp, Eq, Sp, Dd, Close,
        Sp, Land, Sp, Open, F.Id("y"), Sp, Eq, Sp, F.Id("t"), Sp, Lor, Sp,
        F.Id("y"), Sp, Eq, Sp, F.Id("u"), Close,
        Sp, Land, Sp, A, Sp, Le, Sp, F.Id("x"), Plus, F.Id("y"), Sp, Land, Sp,
        F.Id("x"), Plus, F.Id("y"), Sp, Le, Sp, B, Sp, CloseBrace);

    private static Formula LowerFormula() => Disp(Seq(
        RealQuantifier(C, Comma, Dd, Comma, F.Id("t"), Comma, F.Id("u"), Comma, A, Comma, B),
        Open, Call("Nontrivial", F.Id("S")), Sp, Land, Sp,
        C, Plus, F.Id("t"), Sp, Lt, Sp, B, Sp, Land, Sp,
        B, Sp, Lt, Sp, Dd, Plus, F.Id("t"), Close, Sp, Implies, Sp,
        Open, A, Sp, Le, Sp, C, Plus, F.Id("t"), Sp, Land, Sp,
        C, Plus, F.Id("t"), Sp, Le, Sp, B, Close));
}
