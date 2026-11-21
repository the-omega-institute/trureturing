using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class CompactMatchedReplacementBranchGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matched replacement on the compact rank-one flat carrier separates the generalized physical strategies by shared-classical branch count.",
        H("Compact Matched Replacement Branch Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-matched-replacement-branch-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap.result"),
                H("A physical benchmark with a dimension-dependent branch lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For m positive, encode the actual compact flat rank-one sectors by the isometry which copies the sector label to both physical parties. Construct a replacement channel with m shared branches. Each branch deterministically prepares the same chosen label on both sides, with weight 1/m. The construction uses native trace-preserving completely positive channels and their full-matrix mixture realization.")),
                    Paragraph(Text(
                        "Any competitor with r shared classical product branches acts on the encoded basis witness as a weighted mixture of product states. Computational-basis measurement gives a mixture of pairs of independent local distributions. Their overlap with the uniformly matched label distribution is at most the square root of r/m, by capped arithmetic-geometric mean and Cauchy-Schwarz. Diagonal measurement cannot increase the trace norm, so the native unhalved diamond distance is at least twice one minus the square root of r/m.")),
                    Paragraph(Text(
                        "The lower bound concerns approximation of this specific attainable replacement channel. It does not change the previously established optimum for the original coherent flat target, and the replacement operation does not impose exact-output calibration on every logical basis sector.")))),
            Describe.Lean(
                DescribeId.Create("replacement-diamond-exact"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap.replacer_diamond_exact"),
                H("Reference-stabilized distance of native replacement channels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the finite input carrier has an element. If both native channels replace the input by a fixed matrix multiplied by its trace, every reference-amplified output difference is the trace-one positive marginal on the reference tensored with the output-matrix difference. The trace norm is multiplicative for this tensor, so the native diamond distance is exactly the trace norm of the difference between the two replacement outputs.")))),
            Paragraph(Text(
                "Paper consequence, not an additional Lean claim: if m equals r times k squared, choose r equiprobable branches supported on disjoint k-label blocks, with both local preparations independently uniform on their branch's block. The distance is exactly twice one minus 1/k, meeting the lower bound. In particular four matched labels have distance exactly one from the nearest product strategy, and exact realization for general m requires m branches. This resource separation is for the replacement benchmark, not a new coherent-target optimum.")))));
}
