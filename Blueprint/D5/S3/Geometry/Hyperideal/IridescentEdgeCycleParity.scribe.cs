using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class IridescentEdgeCycleParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite normal-edge cycle with a transported pair of distinct non-target colors has even length.",
        H("Parity from transported rainbow endpoint colors"),
        Blocks(
            Paragraph(Text("A RainbowCycle consists of a finite set of occurrences, a successor permutation, and two colors recorded from the chosen endpoint of a target edge. The two colors are distinct at every occurrence, and the successor exchanges the two colors.")),
            Describe.Lean(
                DescribeId.Create("rainbow-cycle-even-card"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/IridescentEdgeCycleParity.even_card_of_rainbow_cycle"),
                H("Transported endpoint colors force even length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ordering the two distinct colors gives a Boolean orientation. The successor reverses this orientation. Choosing the successor in one orientation and its inverse in the other produces a fixed-point-free involution, so the finite occurrence set has even cardinality."))),
                DescribeRole.Theorem))));
}
