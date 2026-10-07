using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class DriftVarianceBoundedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Drift Variance Bounded"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate drift variance bounded to the stochastic ellipsoid construction.")),
            Node("claim-1", "variance_trunc_le", "variance trunc le",
                "Popoviciu, per summand.", DescribeRole.Theorem),
            Node("claim-2", "variance_sum_le", "variance sum le",
                "The drift proxy's variance, from independence and a pathwise cap. No Gaussian moment of any order is used.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
