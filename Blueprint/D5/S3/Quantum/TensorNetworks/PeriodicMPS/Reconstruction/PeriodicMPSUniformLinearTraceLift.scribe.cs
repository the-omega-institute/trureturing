using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformLinearTraceLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift";
    private const string Title = "Weighted invariant recovery from the full periodic projector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformlineartracelift-result"),
            DeclarationHandle.Create(Module + ".lift_eq_of_readColumn_ne_zero"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every length 6 + r, a nonzero linearly read column of the full projector determines the weighted invariant projector at every point of the compact graph. The proof first reconstructs the weighted coordinates on actual tensors and then extends the identity by continuity on the nonzero-column locus."))),
            DescribeRole.Theorem))));
}
