using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class BallNetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Volumetric finite nets in finite-dimensional real normed spaces.",
        H("Volumetric covering of the unit ball"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-ballnet-exists-finset-net-unitball"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/BallNet.exists_finset_net_unitBall"),
                H("Internal finite net with a volume bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Take a maximal epsilon-separated subset of the given subset of the closed unit ball. Disjoint balls of radius epsilon over two have total Haar measure bounded by that of the ball of radius one plus epsilon over two. This gives the displayed cardinality in the real dimension."))),
                DescribeRole.Theorem))));
}
