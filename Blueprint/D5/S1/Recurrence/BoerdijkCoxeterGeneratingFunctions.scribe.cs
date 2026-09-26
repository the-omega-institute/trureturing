using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BoerdijkCoxeterGeneratingFunctionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/kagey2026a400216tetrahelix");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered Boerdijk-Coxeter tetrahelix has Kagey's three exact rational coordinate series.",
        H("Tetrahelix Coordinate Generating Functions"),
        Blocks(
            Paragraph(Text(
                "The vertices begin in the source's order: (-1,-1,-1), (-1,1,1), "
                    + "(1,-1,1), (1,1,-1). Each next vertex is the reflection of "
                    + "the oldest across the face through the other three. The "
                    + "source scales coordinates by one through index three and "
                    + "by a power of three thereafter.")),
            Node("Point", "Rational points",
                "A point has three rational coordinates, indexed by Fin 3."),
            Node("sqDist", "Squared distance",
                "The sum of the three squared coordinate differences."),
            Node("faceCenter", "Face centroid",
                "The coordinatewise average of three face vertices."),
            Node("reflected", "Reflected vertex",
                "Twice the face centroid minus the oldest vertex, coordinate by coordinate."),
            Node("regular", "Regular tetrahedron",
                "The six squared edge lengths of four vertices are equal."),
            Node("faceOrthogonal", "Orthogonality to a face vertex",
                "The vector from the face centroid to the old vertex is perpendicular "
                    + "to the vector from that centroid to the selected face vertex."),
            Node("faceNoncollinear", "Noncollinear face",
                "The third face vertex is not on the rational affine line through "
                    + "the first two."),
            Node("vertex", "Ordered helix vertices",
                "The unique order-four recurrence solution with the source's ordered "
                    + "initial tetrahedron."),
            Node("scale", "Coordinate scaling",
                "The factor is one through index three, then 3 to the power n minus three."),
            Node("scaled", "Scaled coordinate",
                "The selected coordinate of vertex n multiplied by the source scaling factor."),
            Describe.Lean(
                DescribeId.Create("tetrahelix-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The three conjectured coordinate series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural index, the face has noncollinear "
                        + "vertices and a nonzero normal. The next vertex is "
                        + "its face reflection. The x, y and z generating functions equal "
                        + "the three rational formal power series in OEIS A400216, "
                        + "A400217 and A400218. The proof uses a scaled order-four "
                        + "recurrence and cancels one nonzero factor for z. The "
                        + "OEIS asymptotic comparison of 24 orientations is not "
                        + "part of the Lean statement."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a400216-a400218-tetrahelix-generating-functions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Node(string name, string title, string description) =>
        Describe.Lean(DescribeId.Create("tetrahelix-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
