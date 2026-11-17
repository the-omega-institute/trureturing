using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CommonBandSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed signed perturbation forces near-optimal cross energy while preserving a common variance band.",
        H("Common-band near-optimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign-choices"),
                DeclarationHandle.Create(Prefix + "signChoices"),
                H("Three perturbation signs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The available perturbation coefficients form the finite set {-1,0,1}."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-response-affine"),
                DeclarationHandle.Create(Prefix + "profileResponse_affine"),
                H("Linearity of the price-weighted response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded measurable E and F, an integrable profile g, any exponent theta and scalar t, and x>=3, the response to E+tF equals the response to E plus t times the response to F."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-cross-affine"),
                DeclarationHandle.Create(Prefix + "profileCross_affine"),
                H("Quadratic expansion of cross energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded measurable E and F, arbitrary exponents and scalar t, and X>=3, the cross energy of E+tF equals that of E, plus t times the sum of the two separately oriented mixed-response integrals, plus t^2 times the cross energy of F. No symmetry of the mixed integrals is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-cross-quadratic-identity"),
                DeclarationHandle.Create(Prefix + "profileCross_quadratic_identity"),
                H("Cancellation of the mixed terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded measurable E and F and X>=3, the cross energies of E+F and E-F, minus twice the cross energy of E, equal twice the cross energy of F."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-cross-fixed-sign"),
                DeclarationHandle.Create(Prefix + "profileCross_fixed_sign"),
                H("One sign on infinitely many centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any two locally bounded measurable error functions and any exponent pair, there is a fixed sign in {-1,0,1} such that, on infinitely many spike centers, the absolute cross energy of E plus that sign times F is at least half the absolute cross energy of F. The sign is selected before any lower-bound constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("von-koch-affine-spikes"),
                DeclarationHandle.Create(Prefix + "vonKoch_affine_spikes"),
                H("Preservation of a von Koch bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a<b and an admissible sparse perturbation, if E satisfies the bound O(sqrt(x)log(x)^2), then E plus any fixed real multiple of the perturbation satisfies the same bound, in the exact VonKochBoundFor predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-band-near-optimality"),
                DeclarationHandle.Create(Prefix + "common_band_near_optimality"),
                H("Near-optimality on a common variance band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 0<alpha<a<b<beta<1. Suppose E is locally bounded and measurable and its cumulative variance is asymptotic to Yu log(Y/u), uniformly for Y^alpha<=u<=Y^beta. There are an admissible starting index and a fixed sign epsilon in {-1,0,1} such that E*=E+epsilon F is locally bounded and measurable and preserves that uniform asymptotic. For every c<(b-a)^2/8, arbitrarily large real X satisfy c X^(1-b)log(X)^3/log(log(X)) <= |C(E*,X)|. For every eta>0, C(E*,X) is not O(X^(1-b)log(X)^(3-eta)). A von Koch bound for E is preserved for this same E*. Together with band_asymptotic_affine, perturbation_pointwise_bound, and vonKoch_affine_spikes, this is Theorem 492.5: both signs preserve the variance asymptotic, the perturbation has the stated pointwise bound, and both signs preserve a von Koch bound. The claim concerns the abstract variance interface; it supplies no arithmetic lower bound for psi-id."))),
                DescribeRole.Theorem))));
}
