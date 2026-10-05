using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale38RawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-frontier obstructions to raw endpoint targets in nested compensation families.",
        H("Scale38 Raw Endpoint Exclusions"),
        Blocks(
            Paragraph(Text(
                "The nested compensation family contains one baseline, enlarged-slot members X_j, "
                + "and contracted-position members Y_i. The X indices begin at one and the Y indices at zero. "
                + "A raw endpoint admits a finite safe sequence of target-leaf queries from the full family: "
                + "each branch group and each absent group has at most one surviving member, "
                + "and only the target survives the complete sequence.")),
            Describe.Lean(DescribeId.Create("scale38-raw-endpoint-exclusions"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.result"),
                H("Excluded enlarged and contracted positions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every k at least one, X_j with 2 at most j at most k is not a raw endpoint, "
                        + "and Y_i with i + 3 at most k is not a raw endpoint. "
                        + "For X_j the indistinguishable competitors are Y_(j-2) and Y_(j-1); "
                        + "for Y_i they are X_(i+2) and X_(i+3).")),
                    Paragraph(Text(
                        "The complete labelled frontier supplies every target leaf. "
                        + "The two chosen competitors reply equally on each of its blocks. "
                        + "At a matching leaf reply both survive; at a branch or absent reply both would "
                        + "belong to the same group, contradicting safety. "
                        + "Thus a safe sequence cannot remove the pair.")),
                    Paragraph(Text(
                        "At k = 2, X_2 has nineteen leaves in four blocks of sizes 3, 8, 5 and 3. "
                        + "The replies of Y_0 and Y_1 on these blocks are matching, absent, absent and branch. "
                        + "These exclusions leave the baseline, X_1 and the last two contracted positions "
                        + "as the possible targets; their realization and exact paid sets require separate scans."))),
                DescribeRole.Theorem))));
}
