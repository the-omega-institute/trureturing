using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class PositiveLaplacePoleObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity bounds the zeta residues of a continued Laplace transform.",
        H("Positive Laplace transforms and zeta poles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("laplace-integrable"),
                DeclarationHandle.Create(Prefix + "laplace_integrable"),
                H("Convergence throughout the regular real ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let mu be a positive measure supported on nonnegative reals, with Laplace integral L(s) converging for every real part greater than B. Let x0>1 and let R be holomorphic for Re(s)>a. Suppose in the initial overlap L(s)=e*P(s)+R(s)+k*x0^(-s)/s, where P(s) is minus one half the logarithmic derivative of (z-1)*zeta(z), evaluated at z=s+1/2. Then the defining integral converges for every real sigma>max(a,0). Multiplication by s times the normalized zeta factor propagates the initial identity on the connected convergence domain. The normalized factor has no positive real zeros. The nonnegative Laplace boundary theorem therefore excludes a convergence boundary on the available real ray."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-positive-pole"),
                DeclarationHandle.Create(Prefix + "no_positive_pole"),
                H("Exclusion of a positive translated zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the preceding hypotheses, assume |e|=1. Every nontrivial zeta zero rho satisfies Re(rho)-1/2<=max(a,0). Otherwise its translated pole lies in the interior of actual Laplace convergence. The actual transform is analytic there, whereas its continued expression has nonzero residue -e*m/2 for the positive zero multiplicity m. Multiplication by the distance from the pole gives incompatible limits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-pole-budget"),
                DeclarationHandle.Create(Prefix + "critical_pole_budget"),
                H("The one-half budget at an imaginary-axis pole"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same hypotheses, assume a<0, |e|=1, and let rho be a nontrivial zero with Re(rho)=1/2. Then k>=1/2. For sigma tending to zero from above, sigma*L(sigma) tends to k, while sigma*L(sigma+i*Im(rho)) tends to -e*m/2. The triangle inequality for the same positive integral bounds the modulus of the second expression by the first real expression. Taking limits gives m/2<=k, and m>=1 proves the assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-axis-limits"),
                DeclarationHandle.Create(Prefix + "imaginary_axis_limits"),
                H("Boundary limits on the imaginary axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose a<0 in the positive Laplace representation, with real coefficient e. For every real t the limit of sigma*G(sigma+i*t) as sigma decreases to zero exists. At t=0 its value is k. At a critical zero rho=1/2+i*t the limit is -e*zeroMult(rho)/2, where zeroMult is the canonical analytic order and is positive. The local analytic-unit factorization identifies the multiplicity in the logarithmic derivative residue with this order. At every nonzero regular frequency the limit is zero. The actual integral agrees with the continued expression throughout the positive half-plane wherever its factors are regular. At the origin only the term k*x0^(-s)/s contributes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-zeros-budget"),
                DeclarationHandle.Create(Prefix + "critical_zeros_budget"),
                H("The finite critical-zero budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same assumptions e=1 and a<0, let Z be any finite set of nontrivial zeros on Re(rho)=1/2. Then card(Z)<=16*k^2. The imaginary parts are distinct and nonzero. All boundary values away from zero have nonpositive real part, and each zero contributes a real value at most -1/2. The same-sign positive-definiteness budget with c=1/2 gives card(Z)/4<=4*k^2. The estimate needs no assumption of linear independence among the imaginary parts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-window-budget"),
                DeclarationHandle.Create(Prefix + "critical_window_budget"),
                H("The multiplicity budget in a short interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same assumptions e=-1 and a<0, there is delta>0 such that every finite critical-zero family whose imaginary parts have pairwise distance less than delta has total multiplicity at most 4*k^2. The nonvanishing of zeta at 1/2 and continuity give a zero-free interval of frequencies about the origin, so the boundary function vanishes at every nonzero difference in the family. The gap positive-definiteness budget gives the sum of squared boundary moduli at most k^2. A zero of positive integer multiplicity m contributes m/2, and m<=m^2 then bounds the sum of canonical multiplicities."))),
                DescribeRole.Theorem))));
}
