using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class DriftChargeTotalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Drift Charge Total"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate drift charge total to the stochastic ellipsoid construction.")),
            Node("claim-1", "driftCharge", "drift Charge",
                "The drift charge, exactly the bracket of StoppedShortfall.logDet_stopped_ge_final.", DescribeRole.Definition),
            Node("claim-2", "driftCen", "drift Cen",
                "The centring constant: the mean of the chi-square half only.", DescribeRole.Definition),
            Node("claim-4", "integral_driftCharge_sub_cen_sq_le", "integral drift Charge sub cen sq le",
                "The centred second moment.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
