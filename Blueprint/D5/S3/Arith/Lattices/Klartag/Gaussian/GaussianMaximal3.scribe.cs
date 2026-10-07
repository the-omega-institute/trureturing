using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GaussianMaximal3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("Gaussian Maximal3"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal3 to the stochastic ellipsoid construction.")),
            Node("claim-4", "exp_one_le_2dN", "exp one le 2d N",
                "exp 1 ≤ 2·d·N. At n ≥ 3 the right side is at least 36.", DescribeRole.Theorem),
            Node("claim-5", "cAdopted", "c Adopted",
                "The chain's adopted scale, c = √h with h = ParamsAdopted2.stepSizeAdopted2 n.", DescribeRole.Definition),
            Node("claim-9", "maximalAtAdopted_adopted", "maximal At Adopted adopted",
                "MaximalAtAdopted with no hypothesis but 3 ≤ n.", DescribeRole.Theorem),
            Node("claim-10", "integrableAtIndex_adopted", "integrable At Index adopted",
                "IntegrableAtIndex with no hypothesis but 3 ≤ n.", DescribeRole.Theorem),
            Node("claim-11", "B_adopted_le", "B adopted le",
                "B_adopted n ≤ 5·√(h·d)·√(log n) for n ≥ 2 073 600. The max is the first term because √(h·d)·(2·log K + 2) ≤ 28·n^{−2.5} < 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
