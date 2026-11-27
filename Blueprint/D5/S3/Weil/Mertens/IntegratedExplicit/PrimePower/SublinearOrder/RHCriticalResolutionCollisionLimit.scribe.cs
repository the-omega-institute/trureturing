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
            Paragraph(Text("The positive cutoff includes zeros whose ordinate equals T and counts analytic multiplicities. The harmonic weight at gamma is m(gamma) gamma/(1/4+gamma^2). Write W(T) for the sum of the weights. The inclusive hard-collision mass E_n(r) sums the products of original multinomial weights over ordered pairs of degree-n occupation vectors with frequency difference of magnitude at most r. The scale s_n is sqrt(n P_2(T_n)/2), with P_2 the second pair moment for the normalized weights.")),
            Paragraph(Text("RH denotes the Riemann hypothesis. M denotes the following uniform upper bound: for each fixed A>1 and delta>0, for all sufficiently large T and every real t with log(T)<=|t|<=A log(T), the Montgomery sum at alpha=t/log(T) is at most delta log(T). Here the pair weight is 4/(4+(gamma-gamma')^2) and the normalization is 2 pi/(T log(T)).")),
            Describe.Lean(DescribeId.Create("harmonic-zeta-critical-collision-limit"),
                DeclarationHandle.Create(Owner + ".harmonic_zeta_critical_collision_limit"),
                H("Conditional Gaussian collision limit at critical resolution"),
                StatementSource.FromAuthor(ConditionalLimit()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a cutoff Y>1 with positive total multiplicity N(Y), the phase magnitude lies above the nonnegative tent with central height b and slope Y N(Y). Integrating the squared tent gives b^3 at most (3/2) exp(2/Y) Y N(Y) times the unnormalized Montgomery sum. With zero total multiplicity the phase sum is zero. The assumed pair bound gives cancellation at the two inclusive cutoffs T and 3T/4. Their difference supplies the harmonic phase deficit above log(T). The finite Landau bound supplies the corresponding deficit below log(T) through the existing logarithmic-window estimates.")),
                    Paragraph(Text("The normalized annulus contribution out to A log(T_n) tends to zero for every fixed A>1. The relative Fejer tail is bounded by 64/(a A), which can be made arbitrarily small by selecting A before taking the limit in n. The same argument applies to each fixed neighboring resolution, so the two-sided secant result recovers the inclusive hard-band constant.")),
                    Paragraph(Text("The classical pair-correlation conjecture would supply the upper bound on these bands. The long-band estimate is an explicit premise here. The argument requires an eventual positive lower bound on epsilon_n log(T_n)."))),
                DescribeRole.Theorem))));

    private static Formula ConditionalLimit()
    {
        Formula n = F.Id("n");
        Formula scale = new Formula.Subscript(F.Id("s"), n);
        Formula resolution = new Formula.Subscript(F.Varepsilon, n);
        Formula height = new Formula.Subscript(F.Id("T"), n);
        Formula start = new Formula.Subscript(F.Id("n"), F.D(0));
        Formula bound = F.Id("a");
        Formula logHeight = F.Seq(F.Log, F.Open, height, F.Close);
        Formula squaredLog = F.Seq(F.Open, logHeight, F.Close, F.Caret, F.Grp(F.D(2)));
        Formula mass = F.Seq(Call("W", height), F.Caret, F.Grp(Multiply(F.D(2), n)));
        Formula collision = F.Seq(new Formula.Subscript(F.Id("E"), n), F.Open, resolution, F.Close);
        Formula normalized = F.Seq(F.Frac,
            F.Grp(Multiply(scale, collision)),
            F.Grp(Multiply(resolution, mass)));
        Formula limit = F.Seq(F.Lim, F.Underscore, F.Grp(n, F.Sp, F.To, F.Sp, F.Infty), F.Sp,
            normalized);
        return F.Disp(new Formula.Aligned([
            F.Seq(F.Id("RH"), F.Sp, F.Land, F.Sp, F.Id("M"), F.Sp, F.Land, F.Sp,
                height, F.Sp, F.To, F.Sp, F.Infty, F.Sp, F.Land, F.Sp,
                F.Frac, F.Grp(squaredLog), F.Grp(n), F.Sp, F.To, F.Sp, F.D(0)),
            F.Seq(F.Land, F.Sp, F.Frac, F.Grp(resolution), F.Grp(scale), F.Sp, F.To, F.Sp, F.D(0)),
            F.Seq(F.Land, F.Sp, F.Open, F.Exists, F.Sp, bound, F.Gt, F.D(0), F.Comma, F.Sp,
                F.Exists, F.Sp, start, F.Comma, F.Sp, F.Forall, F.Sp, n, F.Ge, F.Sp, start, F.Comma, F.Sp,
                F.D(0), F.Lt, resolution, F.Sp, F.Land, F.Sp, bound, F.Le, F.Sp,
                Multiply(resolution, logHeight), F.Close),
            F.Seq(F.Longrightarrow, F.Sp, Equal(limit,
                F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.Sqrt, F.Grp(F.Pi))))),
        ]));
    }
}
