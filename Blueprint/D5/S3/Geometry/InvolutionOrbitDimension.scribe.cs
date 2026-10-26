using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class InvolutionOrbitDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/InvolutionOrbitDimension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metric quotient by an isometric involution preserves the Hausdorff dimension "
            + "of every subset of a second-countable metric space, including fixed points.",
        H("Hausdorff Dimension of an Involution Orbit Space"),
        Blocks(
            Definition("action", "representation", "The two-element isometric action",
                "An involutive isometry generates the action of the two-element group. "
                    + "The identity acts trivially and the other element acts by the supplied isometry."),
            Definition("orbit", "Orbit", "The actual finite orbit space",
                "This is the quotient by that action. The metric is the existing finite-action "
                    + "orbit metric: the distance between classes represented by x and y is the "
                    + "minimum of the distance from x to y and from x to the involute of y. "
                    + "The metric uses the quotient topology; fixed points are retained."),
            Definition("projection", "project", "The orbit projection",
                "The projection sends a point to its actual orbit class. It is one-Lipschitz."),
            Describe.Lean(DescribeId.Create("dimension"), DeclarationHandle.Create(Module + "dimH_project"),
                H("Hausdorff dimension is preserved"), StatementSource.FromAuthor(Dimension()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("No freeness, convexity, finite dimension, or invariance of the "
                        + "subset is assumed. The dimension is Hausdorff dimension in the stated metrics.")),
                    Paragraph(Text("Around a point that is moved by the involution, any ball with "
                        + "radius at most one quarter of its displacement maps isometrically to "
                        + "the quotient. Second countability supplies a countable cover by such "
                        + "balls. On the fixed locus the projection is itself an isometry. "
                        + "Countable stability of Hausdorff dimension gives the lower bound; "
                        + "the Lipschitz projection gives the upper bound."))), DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula C(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Dimension()
    {
        var x = F.Id("X");
        var c = F.Id("c");
        var h = F.Id("h");
        var s = F.Id("s");
        return Disp(Seq(Forall, Sp, x, InMacro, C("Type"), Comma,
            OpenBracket, C("MetricSpace", x), CloseBracket, Sp,
            OpenBracket, C("SecondCountableTopology", x), CloseBracket, Comma, RowBreak,
            Forall, Sp, c, InMacro, C("IsometryEquiv", x, x), Comma,
            h, InMacro, C("Involutive", c), Comma, s, InMacro, C("Set", x), Comma,
            C("dimH", C("image", C("project", c, h), s)), Eq, C("dimH", s)));
    }
}
