using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class FragmentLaplaceTransformDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeGaps/FragmentLaplaceTransform.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive the Laplace functional of the weighted Poisson fragment law and the real Laplace transform of its total mass.",
        H("Laplace Transform of the Fragment Law"), Blocks(
            Describe.Lean(DescribeId.Create("exponential-of-negative-finite-sum"),
                DeclarationHandle.Create(Prefix + "exp_neg_ennreal_sum"),
                H("Factor the exponential of a finite sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any finite index set and extended nonnegative real values, the extended-real exponential of the negative sum equals the product of the exponentials of the negative summands. Finite-set induction proves the identity, including infinite summands, using additivity of the exponential."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-poisson-laplace-functional"),
                DeclarationHandle.Create(Prefix + "lintegral_exp_neg_finitePoissonLaw"),
                H("Laplace functional of a finite Poisson law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a finite intensity measure on the real line and any measurable extended nonnegative test function h, the expected exponential of minus the integral of h against the sampled weighted measure equals the exponential of minus the intensity integral of one minus exp(-ofReal(u) h(u)). Conditioning on the Poisson count factors the sampled-location integral into a power; summing those powers with the Poisson weights gives the formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fragment-law-laplace-functional"),
                DeclarationHandle.Create(Prefix + "lintegral_exp_neg_fragmentLaw"),
                H("Laplace functional of the complete fragment law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every real cutoff zeta and measurable extended nonnegative test function h, the Laplace functional of fragmentLaw(zeta) is the exponential of minus the integral of one minus exp(-ofReal(u) h(u)) against reciprocal-location intensity on (0,zeta]. Independence gives the formula for finite sets of dyadic bands, and dominated convergence passes to their countable sum. Almost-sure finiteness identifies that sum with the finite-fragment map despite its zero fallback."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fragment-mass-laplace-transform"),
                DeclarationHandle.Create(Prefix + "integral_exp_neg_mass_fragmentLaw"),
                H("Real Laplace transform of total fragment mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For positive zeta and nonnegative s, the expectation of exp(-s times the total fragment mass) equals exp of the interval integral from zero to zeta of (exp(-s u)-1)/u. Specializing the Laplace functional to the constant test ofReal(s) gives the identity. The bound between zero and s for (1-exp(-s u))/u on the positive cutoff interval supplies integrability for conversion to real integrals."))), DescribeRole.Theorem)
        )));
}
