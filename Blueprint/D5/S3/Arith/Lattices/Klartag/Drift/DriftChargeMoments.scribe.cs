using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class DriftChargeMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Drift Charge Moments"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate drift charge moments to the stochastic ellipsoid construction.")),
            Node("claim-2", "integral_midCap_sq_le", "integral mid Cap sq le",
                "∫ midCap² ≤ K·cstep²·n/m², the same bound variance_M_le carries.", DescribeRole.Theorem),
            Node("claim-3", "integrable_midCap", "integrable mid Cap",
                "midCap itself is integrable: √x ≤ (1 + x)/2.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
