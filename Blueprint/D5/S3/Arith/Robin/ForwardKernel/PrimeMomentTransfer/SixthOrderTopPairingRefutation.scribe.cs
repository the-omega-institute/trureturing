using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SixthOrderTopPairingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sixth-order top pairing transfer is refuted by a positive finite mixture.",
        H("Sixth-order top pairing transfer fails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed sixth-order implication"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim assumes positivity, a quadratic relation, bounded lower distinct-index moments through order five, and a uniform sixth-order distinct pairing defect bound. It concludes that the sixth family moment with unit weights has vanishing normalized pairing defect."))),
                DescribeRole.Definition))));
}
