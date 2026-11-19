using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalPlaquettePhaseDiamondDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One party's plaquette phase bounds the native diamond error without a common quotient.",
        H("A one-party plaquette obstruction for paired recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-native-one-party-plaquette"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond."
                    + "paired_one_party_native_diamond"),
                H("Native one-party plaquette bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one selected pair of two-coordinate fibres, let theta be the "
                        + "first record's principal plaquette argument and p its quarter-angle "
                        + "cosine. The unhalved diamond error is at least p/2 minus 1/(4p), "
                        + "and at least one quarter minus theta squared over 32. A zero phase "
                        + "gives the quarter lower bound.")),
                    Paragraph(Text(
                        "The opposite diagonal gauges preserve the tested entry products. "
                        + "Only the first record's phase is constrained and both cross blocks "
                        + "are contractions. There is no common quotient or entry-dominance "
                        + "hypothesis. The paired channel identity, target coefficient and "
                        + "selected fibre correspondence remain explicit."))),
                DescribeRole.Theorem))));
}
