using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformLinearTraceLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift";
    private const string Title = "Weighted trace coordinates from periodic amplitudes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title, H(Title),
        Blocks(
            Claim("periodicmpslinearlift-trace", "Uniform linear trace-word readout", "linearReadout_traceWord",
                "At length six plus r, six fixed signed contrasts of complete binary amplitudes recover the weighted invariant vector times twice the negative commutator determinant and the trace of the r-th power of the first core. The six degree-six word combinations evaluate to scalar matrices before the extra letters are appended."),
            Claim("periodicmpslinearlift-compact", "Unique lift on the compact graph", "lift_eq_of_readColumn_ne_zero",
                "If the first contrast of a full-projector column is nonzero, the projector of the contrast vector determines the weighted trace projector throughout the compact graph. The condition holds at the independent-set witness for each length."))));

    private static DocumentBlock.Describe Claim(string id, string title, string name, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/czaplinskimichalekseynnaeve2023umps")),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
