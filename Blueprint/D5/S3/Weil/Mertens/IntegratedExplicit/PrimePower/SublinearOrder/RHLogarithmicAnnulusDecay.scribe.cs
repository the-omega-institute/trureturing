using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHLogarithmicAnnulusDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive harmonic phase deficit forces decay of the normalized annulus integral.",
        H("Harmonic logarithmic annulus decay"),
        Blocks(
            Paragraph(Text("Assume RH. Let H collect the hypotheses B>=1, c>0, T_n tending to infinity, eventual positivity of epsilon_n, (log T_n)^2/n tending to zero, and the following phase-deficit condition. For all sufficiently large cutoff heights T, require normalized harmonic score magnitude at most 1-c/log(T) whenever 1/T<=|t|<=B log(T). Let I_n(R) integrate the Fejer kernel of parameter epsilon_n times the score magnitude to power 2n over the interval from -R to R. The scale s_n is the square root of n times the normalized second pair moment divided by two.")),
            Describe.Lean(DescribeId.Create("harmonic-multiple-log-annulus-limit-of-deficit"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay" +
                    ".harmonic_multiple_log_annulus_limit_of_deficit"),
                H("Decay with an arbitrary positive deficit coefficient"),
                StatementSource.FromAuthor(AnnulusLimit()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If the normalized score has a deficit at least c/log(T) for a fixed c>0 across the annulus, its 2n-th power is at most exp(-2cn/log(T)). The bound on the Fejer kernel cancels the normalization by the resolution. The annulus length is at most 2B log(T), and the phase variance bounds the scale by sqrt(n) T. These factors are dominated by the exponential when log(T)^2/n tends to zero."))),
                DescribeRole.Theorem))));

    private static Formula AnnulusLimit()
    {
        var n = F.Id("n");
        var height = new Formula.Subscript(F.Id("T"), n);
        var resolution = new Formula.Subscript(F.Varepsilon, n);
        var scale = new Formula.Subscript(F.Id("s"), n);
        var integral = new Formula.Subscript(F.Id("I"), n);
        var radius = Multiply(F.Id("B"), F.Seq(F.Log, F.Open, height, F.Close));
        var reciprocal = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(height));
        var difference = F.Seq(F.Open, integral, F.Open, radius, F.Close, F.Sp, F.Minus, F.Sp,
            integral, F.Open, reciprocal, F.Close, F.Close);
        return F.Disp(F.Seq(F.Id("H"), F.Sp, F.Longrightarrow, F.Sp,
            F.Lim, F.Underscore, F.Grp(n, F.Sp, F.To, F.Sp, F.Infty), F.Sp,
            F.Frac, F.Grp(scale), F.Grp(resolution), F.Sp, difference, F.Sp, F.Eq, F.Sp, F.D(0)));
    }
}
