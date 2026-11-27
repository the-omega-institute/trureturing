using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Indecomposable maps from finite Hermitian signs"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixconstruction-finitesignsample-unconditional"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.finiteSignSample_unconditional"),
                H("Simultaneous bounds in the sign cube"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each of the three bad events has probability less than one quarter under the same uniform measure. One assignment lies outside their union. The norm bounds give positive semidefiniteness for both trace tests, and the Schmidt bound gives separability after local congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixconstruction-exists-indecomposable-keb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_indecomposable_kEB"),
                H("Indecomposable k-entanglement-breaking maps"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each integer k at least two and every integer d at least 524288 times k cubed, there is a complex-linear k-entanglement-breaking map from the full d by d matrix algebra into itself that is indecomposable."))),
                DescribeRole.Theorem))));
}
