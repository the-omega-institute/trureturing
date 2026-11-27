using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedResidualGainDocument : IScribeDocumentDefinition
{
    private static Formula A => F.Id("A");
    private static Formula N => F.Id("N");
    private static Formula Z => F.Id("z");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Profile => Operator("discrepancyProfile");
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Estimate() => Disp(Seq(
        Exists, Sp, A, InMacro, Sp, Reals, Comma, Quad, D(0), Lt, A, Sp, Land, Sp,
        Open, Exists, Sp, N, InMacro, Sp, Naturals, Comma, Quad,
        Forall, Sp, Z, InMacro, Sp, Integers, Comma, Quad, Sp,
        N, Lt, Left, Lvert, Sp, Z, Right, Rvert, Longrightarrow, Sp,
        A, Cdot, Sp, Call("discrepancyProfile", Z), Caret, Grp(D(2)), Le, Sp,
        Call("actualGenerator", Profile, Z), Close));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact compensated generator has a positive quadratic lower bound on both integer tails.",
        H("Linear gain for the full logarithmic profile"),
        Blocks(Describe.Lean(
            DescribeId.Create("eventual-two-sided-discrepancy-gain"),
            DeclarationHandle.Create(
                "D5/S1/Words/Patterns/Separable/OccupiedResidualGain.eventual_discrepancy_linear_gain"),
            H("One threshold and gain constant for both signs"),
            StatementSource.FromAuthor(Estimate()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The discrepancy profile is the reciprocal of the product of the square root "
                    + "and logarithm of the base two plus the absolute position. "
                    + "The generator is the actual compensated weighted jump series. "
                    + "The integer absolute value of z must strictly exceed the natural threshold N, viewed as an integer.")),
                Paragraph(Text(
                    "Subtracting the finite exponent mixture from the full profile leaves the inverse three-quarter power "
                    + "of the base divided by its logarithm. Convexity gives nonnegative residual increments for jumps "
                    + "that stay on the same side. The remaining crossing jumps have a polynomially small total lower cost. "
                    + "The positive mixture gain absorbs that cost, and evenness transfers the estimate to negative positions."))),
            DescribeRole.Theorem))));
}
