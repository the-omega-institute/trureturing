using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHCriticalPairSumThresholdDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed positive upper threshold for the pair sum is sufficient at critical resolution.",
        H("Positive pair-sum threshold for zeta collisions"),
        Blocks(
            Paragraph(Text("The inclusive cutoff counts each positive ordinate with analytic multiplicity. Write N(Y) for this count and S_Y(t) for its phase sum. In G_Y(t), sum over all ordered pairs of retained ordinate labels, including the diagonal. The summand is the product of the two analytic multiplicities times 4 cos(t (gamma-gamma'))/(4+(gamma-gamma')^2). To obtain G_Y(t) from the normalized Montgomery function, evaluate at alpha=t/log(Y) and multiply by Y log(Y)/(2 pi).")),
            Paragraph(Text("Let c=1/(2 pi). The premise P asserts that a constant kappa in (0,2 c^2/3) satisfies G_Y(t)<=kappa Y log(Y)^2 uniformly on every fixed band log(Y)<=|t|<=A log(Y) for all sufficiently large Y, for each fixed A>1.")),
            Describe.Lean(DescribeId.Create("harmonic-zeta-critical-collision-limit-of-threshold"),
                DeclarationHandle.Create(Owner + ".harmonic_zeta_critical_collision_limit_of_threshold"),
                H("Critical Gaussian collision limit under the positive threshold"),
                StatementSource.FromAuthor(ConditionalLimit()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write W(T) for the total harmonic weight and E_n(r) for the original inclusive hard-collision mass. The scale s_n is sqrt(n P_2(T_n)/2), where P_2 is the second pair moment of the normalized weights. RH denotes the Riemann hypothesis.")),
                    Paragraph(Text("The squared phase peak has exponential energy G_Y(t). A nonnegative profile with central value b and slope bound L lies above max(b-L|u|,0). For r=b/L the energy of this tent is L^2 (r^2-r+(1-exp(-2r))/2), and the tent attains that energy. Bounding the exponential by its minimum on the tent support gives b^3<=(3/2) exp(2/Y) Y N(Y) G_Y(t) with L=Y N(Y). The zero-mass cutoff has zero phase sum.")),
                    Paragraph(Text("Since N(Y)/(Y log(Y)) tends to c, the strict threshold gives a fixed positive fractional deficit for |S_Y(t)|. The harmonic coefficient per multiplicity is at least 1/(2Y) throughout the inclusive cutoff. Monotonicity of the norm deficit under increasing weights and the harmonic mass asymptotic give a positive constant times 1/log(Y) as the normalized deficit.")),
                    Paragraph(Text("The Landau estimate supplies the short-band deficit. Annulus decay and the relative Fejer tail then give the Gaussian constant at every fixed neighboring resolution, which yields the inclusive hard-band limit. The uniform upper bound on G_Y is an arithmetic premise."))),
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
            F.Seq(F.Id("RH"), F.Sp, F.Land, F.Sp, F.Id("P"), F.Sp, F.Land, F.Sp,
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
