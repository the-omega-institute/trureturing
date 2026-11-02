using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class LinearMomentGrowthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Interpolation/LinearMomentGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative exponential growth from a linear upper rate for finite atomic moment positivity.",
        H("Linear moment growth"), Blocks(
            Describe.Lean(DescribeId.Create("linear-moment-growth"),
                DeclarationHandle.Create(Owner + "linear_moment_growth"),
                H("Universal quantitative linear-rate growth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let F:R to R be continuous and even, let m:R to N be arbitrary and eventually at least one, and let c>=0. If for every eta>0 the ratio m(D)/D is eventually at most c+eta, and the full finite-family momentPositive(F,m) telescope holds, then for every beta with 32*c<beta there exists C>0 such that |F(t)|<=C exp(beta |t|) for every real t.")),
                    Paragraph(Text("Fix beta>32*c and set h=2/beta, G(s)=F(h*s), and k(D)=m(h*D). Then h>0 and h*c<1/16. Pulling every finite complex atomic family through x_i to h*x_i preserves all moment annihilation equations, including empty, repeated, overlapping and zero-coefficient families, and transfers eventual positivity from F,m to G,k. The rate hypothesis supplies an eventual k(D)/D<1/16 and the eventual lower bound k(D)>=1.")),
                    Paragraph(Text("At a large real window t, write n=floor(t), r=t-n and k=k(t). The fixed finite Newton estimate from SublinearMomentGrowth applies when 2*k<=n and gives |G(t)|<=envelope G(2*k+1) times the truncated binomial sum. The existing binomial_sum_exp estimate at z=1/4 bounds that sum by exp(8*k+n/2)<=exp(t), while 2*k+1<=t/2. Thus |G(t)|<=envelope G(t/2)*exp(t) for all sufficiently large t.")),
                    Paragraph(Text("The existing envelope_half_step and envelope_dyadic estimates lift this half-radius bound to envelope G(R)<=envelope G(2*T)*exp(2*R) for every nonnegative R by a finite induction. Evenness handles all real arguments. Rescaling back uses 2/h=beta, yielding the displayed bound with C=envelope G(2*T). No initial majorant, monotonicity, fixed order, distinctness, nonempty-family, arithmetic or RH hypothesis is introduced. The theorem remains conditional analytic input and supplies no construction of m or RH result."))),
                DescribeRole.Theorem))));
}
