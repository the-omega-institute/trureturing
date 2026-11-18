using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HuangUnitSupportGapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unit-valued negative-three Huang eigenvector cannot have support twenty-four.",
        H("A gap for unit-valued Huang eigenvectors"),
        Blocks(
            Paragraph(Text(
                "The original signed Huang operator on Q9 is retained throughout. "
                    + "This obstruction is consumed by the nontrivial four-edge-cut argument "
                    + "toward Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2). "
                    + "The 258-vertex problem and literature novelty remain unresolved.")),
            Describe.Lean(
                DescribeId.Create("huang-unit-support-not-twenty-four"),
                DeclarationHandle.Create(Prefix + "no_unit_support_card_twenty_four"),
                H("Support twenty-four is impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For h : Q9 → ℤ, assume Ah = −3h for the original integer Huang operator, "
                            + "every value is 0, 1 or −1, and exactly twenty-four values are nonzero. "
                            + "These three assumptions imply False. No extra certificate, parity "
                            + "hypothesis or unweighted adjacency operator is substituted.")),
                    Paragraph(Text(
                        "Write h = r + s for its even and odd parts. The cube changes parity "
                            + "along every edge, giving Ar = −3s and As = −3r. Symmetry of the "
                            + "signed matrix equates the two squared norms, so the support of r "
                            + "has twelve vertices. Divisibility of every row Ar by three excludes "
                            + "a singleton neighbor, because its only contribution would be ±1. "
                            + "Equal cube parity gives even Hamming distance via the Boolean ring. "
                            + "CubeTwelveSupport identifies the twelve-point support as a complete "
                            + "nine-point star, a contradiction."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeTwelveSupport"))
        ]));
}
