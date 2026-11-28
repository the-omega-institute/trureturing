using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEAAttainmentBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary entanglement-assisted Singleton attainment is impossible at length eight or greater.",
        H("Excluding binary Singleton attainment at length eight or greater"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-ea-attainment-bridge-claim"),
                DeclarationHandle.Create(Module + "claim"),
                H("A code at length at least eight with at most three zeros outside the radical"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The binary symplectic code has dimension eight and its radical has dimension four. "
                    + "Every word outside the radical vanishes on at most three sites, "
                    + "where vanishing means that both binary coordinates are zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-ea-attainment-bridge-result"),
                DeclarationHandle.Create(Module + "result"),
                H("Exclusion at every length from eight onward"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For length at least nine, the coordinate-kernel bounds give radical site ranks "
                        + "at most one and support size at most ten. At length eight, a positive "
                        + "radical kernel on each pair bounds the joint rank by three. "
                        + "The length-eight shortening theorem therefore rules out every surjective "
                        + "radical site. The support size is at most eight in this case.")),
                    Paragraph(Text(
                        "Restrict both spaces to the radical's occupied sites and relabel those sites. "
                        + "The projection is injective on the code, preserves its pairing with the radical, "
                        + "and can only decrease each nonradical word's zero count. Each occupied "
                        + "radical image has dimension one. The rank-one bridge excludes the resulting spaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-ea-attainment-bridge-conditional-refutation"),
                DeclarationHandle.Create(Module + "refute_attainment_of_length_seven_rank_two"),
                H("Reduction of exact attainment to the length-seven rank-two case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact attainment requires weight at least n − 3 outside the radical and a "
                    + "nonradical word of weight exactly n − 3. The lower bound implies the three-zero "
                    + "condition. The radical needs at least seven occupied sites, and the general "
                    + "rank-one exclusion also rules out length seven when no radical site is surjective. "
                    + "An exclusion at length seven with a surjective radical site would therefore "
                    + "refute exact attainment."))),
                DescribeRole.Theorem))));
}
