using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class S154B0SchurCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/S154B0SchurCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite certificates for the registered rank-three B0 recovery probe.",
        H("S.154 B0 Schur certificate"),
        Blocks(
            Entry("inverse", "b0_inverse_identity", "The diagonal inverse identities",
                "The displayed diagonal matrix with entries 6, 8, 56/5, 56/5 and 3 is both a left and a right inverse of the displayed positive diagonal matrix with entries 1/6, 1/8, 5/56, 5/56 and 1/3.",
                DescribeRole.Theorem),
            Entry("schur", "b0_schur_interface", "The exact Schur interface",
                "For the fixed real matrices E0, E1 and T, the weighted sum (E0 transpose Y inverse E0 + E1 transpose Y inverse E1)/16 + T transpose Y inverse T/4, with the displayed diagonal inverse, equals the diagonal matrix with entries 1, 1 and 7/50. This is the finite Schur interface used by the rank-three B0 dual certificate.",
                DescribeRole.Theorem),
            Entry("trace", "b0_trace_bound", "The strict trace slack",
                "The rational trace value 45/56 is strictly smaller than (1 + 1/square-root of 2)/2.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
