using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHCriticalResolutionCollisionLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian hard collisions at positive critical resolution under an upper Montgomery bound.",
        H("Collision limit at critical resolution"),
        Blocks(
            Paragraph(Text("The positive cutoff includes zeros whose ordinate equals T and counts analytic multiplicities. The harmonic weight at gamma is m(gamma) gamma/(1/4+gamma^2). Write W(T) for the sum of the weights. The inclusive hard-collision mass E_n(r) sums the products of original multinomial weights over ordered pairs of degree-n occupation vectors with frequency difference of magnitude at most r.")),
            Describe.Lean(DescribeId.Create("harmonic-zeta-critical-collision-limit"),
                DeclarationHandle.Create(Owner + ".harmonic_zeta_critical_collision_limit"),
                H("Conditional Gaussian collision limit at critical resolution"),
                StatementSource.FromAuthor(LimitValue()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume RH and the uniform upper Montgomery bound. For every fixed A>1 and every delta>0, the normalized Montgomery pair sum at alpha=t/log(T) is at most delta log(T) for all sufficiently large T and log(T)<=|t|<=A log(T). The pair weight is 4/(4+(gamma-gamma')^2), and the normalization is 2 pi/(T log(T)).")),
                    Paragraph(Text("Let T_n tend to infinity with log(T_n)^2/n tending to zero. Define s_n=sqrt(n P_2(T_n)/2) using the normalized second pair moment. The resolutions epsilon_n are eventually positive, epsilon_n/s_n tends to zero, and there is a positive constant a such that eventually epsilon_n log(T_n)>=a.")),
                    Paragraph(Text("At each cutoff Y, a phase peak of magnitude b retains magnitude at least b/2 throughout an interval of radius b/(2 Y N(Y)). The exponentially weighted square integral on this interval bounds b^3 by 4 e Y N(Y) times the unnormalized Montgomery sum. The assumed pair bound then gives cancellation at the two inclusive cutoffs T and 3T/4. Their difference supplies the harmonic phase deficit above log(T). The finite Landau bound supplies the corresponding deficit below log(T) through the existing logarithmic-window estimates.")),
                    Paragraph(Text("The normalized annulus contribution out to A log(T_n) tends to zero for every fixed A>1. The relative Fejer tail is bounded by 64/(a A), which can be made arbitrarily small by selecting A before taking the limit in n. The same argument applies to each fixed neighboring resolution, so the two-sided secant result recovers the inclusive hard-band constant.")),
                    Paragraph(Text("The classical pair-correlation conjecture would supply the upper bound on these bands. The long-band estimate is an explicit premise here. The argument requires an eventual positive lower bound on epsilon_n log(T_n)."))),
                DescribeRole.Theorem))));

    private static Formula LimitValue()
    {
        Formula n = F.Id("n");
        Formula scale = new Formula.Subscript(F.Id("s"), n);
        Formula resolution = new Formula.Subscript(F.Varepsilon, n);
        Formula height = new Formula.Subscript(F.Id("T"), n);
        Formula mass = F.Seq(Call("W", height), F.Caret, F.Grp(Multiply(F.D(2), n)));
        Formula collision = F.Seq(new Formula.Subscript(F.Id("E"), n), F.Open, resolution, F.Close);
        Formula normalized = F.Seq(F.Frac,
            F.Grp(Multiply(scale, collision)),
            F.Grp(Multiply(resolution, mass)));
        Formula limit = F.Seq(F.Lim, F.Underscore, F.Grp(n, F.Sp, F.To, F.Sp, F.Infty), F.Sp,
            normalized);
        return F.Disp(Equal(limit, F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.Sqrt, F.Grp(F.Pi)))));
    }
}
