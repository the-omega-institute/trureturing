using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FourRateSupermodularityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.";

    public DocumentDefinition Create()
    {
        Formula x = F.Id("X"), y = F.Id("Y"), real = F.Id("Real");
        Formula vector = Seq(Call("Fin", D(4)), Longrightarrow, Sp, real);
        Formula gx = Call("ceilingRate", x);
        Formula xz = Call("coordinate", x, D(0)), xo = Call("coordinate", x, D(1));
        Formula xt = Call("coordinate", x, D(2)), xr = Call("coordinate", x, D(3));
        Formula threshold = Fraction(D(1, 6), D(7, 2, 9));
        Formula tail = Fraction(D(1, 9, 4, 4), D(3, 9, 0, 6, 2, 5));
        Formula slope = Fraction(D(1, 1, 1, 6, 5, 2, 9), D(8, 0, 6, 6, 2, 5));
        Formula intercept = Seq(Minus, Fraction(D(1, 5, 1, 2, 9, 8), D(2, 6, 8, 8, 7, 5)));
        Formula cube = All("i", Call("Fin", D(4)),
            Seq(Fraction(D(2), D(9)), Le, Call("coordinate", x, F.Id("i")), Land,
                Call("coordinate", x, F.Id("i")), Le, Fraction(D(6), D(2, 5))));
        Formula envelope = Seq(gx, Star, Open, D(1), Plus, xo, Plus, xo, Star, xt, Close,
            Minus, Fraction(Seq(slope, Star, gx, Star, Open, D(1), Plus, xz, Close),
                Seq(gx, Plus, xz)), Minus, Open, intercept, Close);
        Formula statement = All("X", vector, All("Y", vector,
            Seq(Open, Call("InCube", x), Land, Call("InCube", y), Close, Rightarrow,
                Call("H", x), Plus, Call("H", y), Le,
                Call("H", Call("inf", x, y)), Plus, Call("H", Call("sup", x, y)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact four-rate min-envelope satisfies the lattice inequality on its full closed real cube.",
            H("Supermodularity of the four-rate envelope"), Blocks(
                Paragraph(Text("Coordinates are indexed by Fin(4), from zero to three, and take arbitrary real values. Infimum and supremum of vectors are pointwise minimum and maximum. The lower and upper rate bounds are 2/9 and 6/25. The threshold T is 16/729, the tail bound q is 1944/390625, the slope kappa is 1116529/806625, and the intercept zeta is -151298/268875.")),
                Describe.Lean(DescribeId.Create("four-rate-ceiling"),
                    DeclarationHandle.Create(Prefix + "ceilingRate"),
                    H("The two-branch upper rate"),
                    StatementSource.FromAuthor(Disp(All("X", vector,
                        Seq(gx, Eq, Call("min",
                            Fraction(threshold, Seq(xo, Star, xt)),
                            Fraction(tail, Seq(xo, Star, xt, Star, xr))))))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The two values agree when coordinate three equals h=q/T=177147/781250, which lies strictly between the two rate bounds. For X in the closed cube [2/9,6/25]^4, the minimum uses the threshold branch below h and the tail branch above h."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("four-rate-envelope"),
                    DeclarationHandle.Create(Prefix + "envelope"),
                    H("The scalar envelope"),
                    StatementSource.FromAuthor(Disp(All("X", vector,
                        Seq(Call("envelope", x), Eq, envelope)))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The rational correction uses coordinate zero and the same upper rate."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("four-rate-adjustment"),
                    DeclarationHandle.Create(Prefix + "H"),
                    H("The adjusted envelope"),
                    StatementSource.FromAuthor(Disp(All("X", vector,
                        Seq(Call("H", x), Eq, Call("envelope", x), Minus, xz, Star, xo)))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The adjustment subtracts the product of coordinates zero and one."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("four-rate-cube"),
                    DeclarationHandle.Create(Prefix + "InCube"),
                    H("The full closed cube"),
                    StatementSource.FromAuthor(Disp(All("X", vector,
                        Seq(Call("InCube", x), Iff, cube)))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each coordinate varies independently over the closed interval, including both endpoints."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("four-rate-supermodularity"),
                    DeclarationHandle.Create(Prefix + "four_rate_supermodular"),
                    H("The global lattice inequality"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Replace coordinate three by max(h,x3). This transformation preserves pointwise minimum and maximum and sends the cube into itself. The upper rate then equals q/(x1 x2 max(h,x3)), so one rational formula handles both branches and their common seam.")),
                        Paragraph(Text("For the smooth formula, all six coordinate rectangles have nonnegative slack. The rational contribution for coordinates zero and one dominates the product of their increments. For zero paired with either remaining coordinate it is nonnegative; for two distinct active coordinates its factored numerator is nonnegative because x0 x1 x2 x3/q is at most 2/3. Positive reciprocal terms also have nonnegative rectangle slack. The pair of coordinates zero and one absorbs the subtracted product.")),
                        Paragraph(Text("Telescoping these pairwise inequalities proves the vector lattice inequality. Equal coordinates and closed edges are included. The statement supplies a scalar inequality; it asserts no representation, rigidity, exclusion of a zero level, compactness or positive attained minimum for probability flows."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Seq(params Formula[] parts) => F.Seq(parts);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
