using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ProfileQuadraticFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ProfileQuadraticForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The covariance kernel min(s,t) defines a positive quadratic energy on real integrable profiles.",
        H("The quadratic energy of an integrable profile"),
        Blocks(
            Paragraph(Text(
                "For a real Borel integrable function g on (0,1), write "
                + "G_g(r) for the integral of g from r to 1, and Q(g) for "
                + "the double integral of g(s)g(t)min(s,t) on the unit square. "
                + "The quantity profileL1(g) is the integral of |g| on (0,1).")),
            Describe.Lean(
                DescribeId.Create("q-eq-tail-energy"),
                DeclarationHandle.Create(Prefix + "Q_eq_tail_energy"),
                H("Tail-integral representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integrable profile g, Q(g) equals the integral of G_g(r)^2 "
                    + "from 0 to 1. Express min(s,t) as the integral of the product of "
                    + "the two cutoff indicators. The absolute integrand is bounded "
                    + "by |g(s)g(t)| on the unit cube, so Fubini applies. After exchanging "
                    + "the order of integration, the product integral factors as G_g(r)^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sqrt-q-sub-le"),
                DeclarationHandle.Create(Prefix + "sqrt_Q_sub_le"),
                H("Continuity in the L1 distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For integrable profiles f and g, the absolute difference between "
                    + "sqrt(Q(g)) and sqrt(Q(f)) is at most the integral of |g-f|. "
                    + "Use the reverse triangle inequality for the L2 norm of their tail "
                    + "integrals. Each tail integral of g-f is bounded by its L1 norm, "
                    + "and the unit interval has measure one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-pos-iff"),
                DeclarationHandle.Create(Prefix + "Q_pos_iff"),
                H("Strict positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integrable profile g, Q(g)>0 if and only if g is not almost "
                    + "everywhere zero on (0,1). If Q(g)=0, its continuous tail integral "
                    + "vanishes almost everywhere and hence everywhere on [0,1]. "
                    + "The almost everywhere derivative of that primitive then forces "
                    + "g=0 almost everywhere. The converse follows directly from the "
                    + "definition of Q."))),
                DescribeRole.Theorem))));
}
