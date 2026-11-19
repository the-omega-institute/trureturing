using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuRankOneEndpointFloorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The endpoint applies the two local maps on different tensor factors with a diagonal sign conjugation.",
        H("The signed two-mode endpoint"),
        Blocks(
            Paragraph(Text("Write λ = √(2/3). The local map mixes diagonal entries with weights 5/6 and 1/6 and multiplies off-diagonal entries by λ. On the two-mode space, the sign operator is −1 at 10 and +1 at the other three coordinates. The entrywise formula follows by composing the two local maps and the sign conjugations.")),
            Paragraph(Text("A diagonal entry uses the four input entries with respective weights 25/36, 5/36, 5/36 and 1/36. If precisely the second bit changes, the mixed weights are 5λ/6 and λ/6. If precisely the first bit changes, they are 5λ/6 and −λ/6. If both bits change, the entry is multiplied by 2/3 (`A₁_apply`).")),
            Describe.Lean(DescribeId.Create("local-map"), DeclarationHandle.Create(Owner + "localMap"),
                H("Local mixing map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal pair is averaged with weights 5/6 and 1/6. Off-diagonal entries are scaled by λ."))), DescribeRole.Definition))));
}
