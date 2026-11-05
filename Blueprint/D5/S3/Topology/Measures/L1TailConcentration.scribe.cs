using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class L1TailConcentrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small supports for every finite prefix",
        H("Small supports for every finite prefix"),
        Blocks(
            Describe.Lean(DescribeId.Create("eventually-small-cross-tails"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/L1TailConcentration.eventually_small_cross_tails"),
                H("Small supports for every finite prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every L1 sequence f bounded in norm by a real B, every natural N, and every positive real epsilon, all sufficiently large natural K satisfy the following simultaneous condition: for every n <= N and every m, the norm of f(n) restricted literally to tailSet(K,f(m)) is at most epsilon. Finite-family uniform integrability and Markov bounds give the actual quantifiers. No finiteness of mu is needed here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-tail-concentration"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/L1TailConcentration.exists_tail_concentration"),
                H("Recursive concentration on measurable hard tails"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every real L1 sequence f with norm bounded by B, there exist natural sequences j,K, a real sequence c and alpha >= 0. The selector j is strictly increasing, i < K(i), alpha <= c(k), and c tends to alpha. For every fixed k, tailNorm(k,f(j(i))) tends to c(k), while tailNorm(K(i),f(j(i))) tends to alpha. For every h < i, the norm of f(j(h)) restricted to the actual measurable tailSet(K(i),f(j(i))) is at most (1/2)^i. This supplies the summable effects of all later supports on each earlier selected input."))), DescribeRole.Theorem))));
}
