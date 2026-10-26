using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;
internal sealed class FiniteSpectralEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite probability moment optimization with a purity budget.",
        H("Finite spectral envelope"), Blocks(Describe.Lean(
            DescribeId.Create("finite-probability-purity-budget-envelope"),
            DeclarationHandle.Create("D5/S3/Entropy/FiniteSpectralEnvelope.finite_budget_envelope"),
            H("The complete finite simplex"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Minimize the Newton expression for e3 over the compact finite probability simplex with squared sum at most q, where 1/3 <= q <= 3/8. No support bound is assumed. The proof uses a three-coordinate smoothing instead of a differentiable constraint argument.")),
                Paragraph(Text("For 0 < a <= b < c, choose small t > 0 and D=(c-b)^2-2t(b+c-2a)-3t^2 > 0. Replace a by a-t and b,c by the positive roots with sum b+c+t and difference sqrt(D). This preserves mass and squared mass. The change in their product is -t(b-a)(c-a)+t^2(2a-b-c)-t^3 < 0, so their cubic sum strictly decreases. Thus every positive triple of a minimizer has its two larger entries equal.")),
                Paragraph(Text("If at least four entries are positive, choose a smallest entry a. Every other positive entry has a common value x, with a <= x and a+3x <= 1. The total purity is a^2+x(1-a) <= 1/3. A minimizer with purity above 1/3 therefore has exactly three positive entries: support at most two would force purity at least 1/2. Its entries are 1-2x,x,x with x >= 1/3, and its value is E at its actual purity. Monotonicity of E converts this to the prescribed budget q. Minimizers of purity at most 1/3 satisfy the coarse 1/27 bound, which also dominates E(q).")),
                Paragraph(Text("This is classical probability moment optimization, in the adjacent U2/U3 region of the moment boundary discussed by Harremoes, Joint Range of Renyi Entropies, Kybernetika 45 (2009), pages 901-911. The source provides the explicit specialization; no priority or physical realization claim is made."))), DescribeRole.Theorem))));
}
