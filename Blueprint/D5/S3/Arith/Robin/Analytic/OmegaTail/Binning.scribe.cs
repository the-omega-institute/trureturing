using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class BinningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive continuous densities on compact positive intervals admit finite disjoint bins preserving mass and entropy while controlling the logarithmic cost.",
        H("Finite density bins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-bins"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Binning.compact_bins"),
                H("Entropy-preserving finite bins"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let g be continuous on [A,B], where 0<A<B, with 0<g(u)<1. For every eta>0 there is a nonempty finite family of pairwise disjoint intervals (a_j,b_j] with positive lengths and masses r_j strictly between zero and their lengths.")),
                    Paragraph(Text("The bin masses sum exactly to the integral of g. Writing q_j=r_j/(b_j-a_j), the sum of (b_j-a_j)*h(q_j) is at least the integral of h(g), where h is binary entropy. The sum of r_j*log(b_j) is at most the integral of g(u)*log(u) plus eta times the total mass.")),
                    Paragraph(Text("A sufficiently fine uniform subdivision makes log(b_j/a_j) smaller than eta. Jensen's inequality for binary entropy bounds each interval entropy by its average-density entropy. The endpoint logarithmic cost differs from the true cost by at most eta times the interval mass."))),
                DescribeRole.Theorem))));
}
