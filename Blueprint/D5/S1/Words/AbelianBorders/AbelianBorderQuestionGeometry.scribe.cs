using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AbelianBorders;

internal sealed class AbelianBorderQuestionGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/charlier2015abelianbordered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The continuous ternary path stays in a rational-axis cylinder and revisits every "
            + "tangential line with bounded gaps.",
        H("The Geometry of the Ternary Path"),
        Blocks(
            Node("diagonal-axis", "The diagonal axis", "axis",
                AxisFormula(),
                "The axis direction is (1,1,1), a nonzero vector with rational coordinates.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("exposed-vertices", "Four vertices modulo the axis", "vertex",
                VertexFormula(),
                "The representatives are (-3,-3,0), (0,-3,0), (2,2,0), and (0,2,0). Projection by "
                    + "T(p)=(p0-p2,p1-p2) sends them to the four vertices of a quadrilateral containing the "
                    + "projected path.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("continuous-path-geometry", "Cylinder containment and recurrent tangential lines", "geometric",
                GeometricFormula(),
                "Every point of the continuous graph is a convex combination of the four representatives "
                    + "plus a real multiple of the diagonal axis. The four exposed vertex lines each contain a "
                    + "cut point in every window from n through n+60. A supporting hyperplane whose contacts "
                    + "lie on a single axis-parallel line forces that line to be one of these exposed vertex "
                    + "lines. Thus cylinder containment and the required bounded tangential gaps both hold.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula AxisFormula() =>
        Disp(Equal(F.Id("axis"), Seq(Open, D(1), Comma, Sp, D(1), Comma, Sp, D(1), Close)));

    private static Formula VertexFormula() =>
        Disp(Equal(Call("map", F.Id("vertex"), Seq(OpenBracket, D(0), Comma, Sp, D(1), Comma, Sp,
                        D(2), Comma, Sp, D(3), CloseBracket)), Seq(OpenBracket, Seq(Open, Seq(Minus,
                            D(3)), Comma, Sp, Seq(Minus, D(3)), Comma, Sp, D(0), Close), Comma, Sp,
                    Seq(Open, D(0), Comma, Sp, Seq(Minus, D(3)), Comma, Sp, D(0), Close), Comma,
                    Sp, Seq(Open, D(2), Comma, Sp, D(2), Comma, Sp, D(0), Close), Comma, Sp, Seq(Open,
                        D(0), Comma, Sp, D(2), Comma, Sp, D(0), Close), CloseBracket)));

    private static Formula GeometricFormula() =>
        Disp(Call("GeometricHypotheses", F.Id("word")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
