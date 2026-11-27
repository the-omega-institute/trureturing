using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEARankOneBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/BinaryEARankOneBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary rank-one geometry is impossible on a support of at most ten sites.",
        H("Exclusion of binary rank-one support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-ea-rank-one-bridge-claim"),
                DeclarationHandle.Create(Module + "claim"),
                H("The original rank-one support hypotheses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let s be eight, nine, or ten. In the binary X and Z space on s sites, "
                    + "U has dimension eight, H has dimension four, and H is a subspace of U. "
                    + "Every vector of U is orthogonal to H for the symplectic form. "
                    + "At every site the image of H in the two local coordinates has dimension one. "
                    + "Every vector in U outside H has at most three sites where X and Z both vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-ea-rank-one-bridge-support-exclusion"),
                DeclarationHandle.Create(Module + "no_rank_one_of_card_le_ten"),
                H("Rank-one support of at most ten sites is impossible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each site, swap the coordinates if the nonzero radical type has X zero. "
                        + "Otherwise add a multiple of X to Z to put the radical type on the X axis. "
                        + "These changes preserve the local symplectic pairing and the simultaneous zero test. "
                        + "The X restrictions to the sites span the dual of H, so four of them give "
                        + "a coordinate isomorphism from H to the four head bits.")),
                    Paragraph(Text(
                        "A vector of U with Z-head zero can be shifted by H to clear its X-head. "
                        + "A vector outside H would then have four zero sites. Thus the Z-head map on U "
                        + "has kernel H and, by dimension, is onto the four head bits. A linear right inverse "
                        + "followed by subtraction of the radical word with matching X-head provides "
                        + "a linear lift with X-head zero. If a lift has zero Z-tail, pairing it "
                        + "with the four radical head basis vectors forces all its Z-head bits to vanish. "
                        + "The tail map is therefore injective on four bits, requiring four tail sites.")),
                    Paragraph(Text(
                        "Use these head coordinates to write the radical X and logical Z generators as "
                        + "[I | A] and [I | R]. Orthogonality gives ARᵀ = I. "
                        + "A one-site exchange forces R to contain the ones of A. For rows that share "
                        + "a one in some column, a two-site exchange forces agreement in the other "
                        + "row on the support of the first. Comparing row products gives AAᵀ = I. "
                        + "Rows with disjoint supports have dot product zero directly.")),
                    Paragraph(Text(
                        "Sort the nonzero radical tail masks and use that same tail permutation for "
                        + "A, R, and the X lift. Pack the binary words with the four head sites in the "
                        + "low bits. The Gram, syndrome, radical translation, and zero-count identities "
                        + "supply the fields of BinaryEARankOneCore.Core at m = s − 4. "
                        + "Its finite exclusion applies for each of the three tail lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-ea-rank-one-bridge-result"),
                DeclarationHandle.Create(Module + "result"),
                H("The original support hypotheses are inconsistent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exclusion for support of at most ten sites applies to the original claim."))),
                DescribeRole.Theorem))));
}
