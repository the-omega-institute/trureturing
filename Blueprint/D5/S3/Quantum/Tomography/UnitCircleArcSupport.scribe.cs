using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class UnitCircleArcSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retain the unit-circle relation when bounding a complex overlap on a signed-Cayley tube.",
        H("Certified unit-circle arc support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-circle-minor-arc-projection-upper"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/UnitCircleArcSupport."
                    + "unit_circle_minor_arc_projection_upper"),
                H("A nonnegative endpoint dual bounds every point of the minor arc"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Rotate the lower endpoint to (1,0) and write the upper endpoint as (a,b), "
                        + "where a squared plus b squared equals one, a is nonnegative and b is positive. "
                        + "A unit point (x,y) belongs to the minor arc when y is nonnegative and bx-ay "
                        + "is nonnegative. These hypotheses imply (1+a)x+by is at least 1+a.")),
                    Paragraph(Text(
                        "Choose either endpoint e=(ex,ey), with nonnegative real multipliers lambda and mu. "
                        + "If gx=lambda ex-mu(1+a) and gy=lambda ey-mu b, the conclusion is "
                        + "gx x+gy y <= lambda-mu(1+a). The proof writes the slack as the sum of "
                        + "lambda times the unit-vector support slack and mu times the circular-cap slack. "
                        + "The circular-cap step follows from an exact polynomial identity, so no numerical "
                        + "angle or extremum solver is assumed.")),
                    Paragraph(Text(
                        "The research checker uses rational endpoint duals for every relative phase, sums "
                        + "their directional bounds in the same complex plane, and only then bounds the "
                        + "squared modulus. This prevents independent real/imaginary boxes from forgetting "
                        + "unit modulus. The standard Cauchy bound handles a direction whose maximizer is "
                        + "inside the arc. The formal theorem supplies the endpoint-dual component; the "
                        + "Cayley-to-arc adapter, finite interval replay and global cover reflection remain "
                        + "separate obligations. Classical circular-cap geometry is not claimed as new mathematics."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Statement() => Disp(Seq(
        Apply("UnitMinorArc", F.Id("a"), F.Id("b"), F.Id("x"), F.Id("y")),
        Sp, Land, Sp,
        Apply("NonnegativeEndpointDual", F.Id("ex"), F.Id("ey"), F.Id("gx"),
            F.Id("gy"), F.Id("lambda"), F.Id("mu")),
        Sp, Rightarrow, RowBreak,
        Apply("ProjectionUpperBound", F.Id("gx"), F.Id("gy"), F.Id("x"),
            F.Id("y"), F.Id("lambda"), F.Id("mu"), F.Id("a")), Dot));
}
