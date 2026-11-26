using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class MobiusDyadicEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/MobiusDyadicEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative lower bound for cumulative signed Möbius shell energy from each zeta zero in the right half of the critical strip.",
        H("Signed Möbius shell energy forced by a zeta zero"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mobius-dyadic-difference"),
                DeclarationHandle.Create(Prefix + "mobiusDyadicDifference"),
                H("Signed difference at two scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write M(x) for the real sum of μ(n)/n over positive integers n at most the "
                    + "natural floor of x, as defined by mobiusPartialSum. The signed difference "
                    + "at x is M(x) − M(2x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mobius-dyadic-shell-energy"),
                DeclarationHandle.Create(Prefix + "mobiusDyadicShellEnergy"),
                H("Energy of a dyadic shell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural k, E(k) is the Lebesgue integral of the squared signed "
                    + "difference on the half-open interval (2^k, 2^(k+1)]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mobius-prefix-zero-energy"),
                DeclarationHandle.Create(Prefix + "K"),
                H("Exponential energy on a logarithmic prefix"),
                StatementSource.FromAuthor(F.Disp(Scale())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real β and U, K(β,U) is the oriented real interval integral from zero "
                    + "to U. At β = 1/2 it equals U. For β > 1/2 and U tending to infinity "
                    + "it grows on the scale exp((2β − 1)U)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mobius-dyadic-zero-lower-bound"),
                DeclarationHandle.Create(Prefix + "signed_dyadic_eventual_prefix_lower_bound"),
                H("Eventual cumulative shell lower bound"),
                StatementSource.FromAuthor(F.Disp(LowerBound())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each complex zero ρ of the Riemann zeta function with real part "
                        + "at least one half and strictly below one, the positive real c and "
                        + "natural N₀ can depend on ρ. The sum contains precisely the shells "
                        + "with indices k below N, and log is the natural logarithm.")),
                    Paragraph(Text(
                        "The finite convolution of the fractional-part kernel and the weighted "
                        + "Möbius sum gives the exact forcing term. The kernel's vanishing "
                        + "Laplace transform at the shifted zero gives an integrable resolvent. "
                        + "Finite convolution with the signed profile leaves an exponential "
                        + "term of amplitude (1 − exp((ρ − 1) log 2))/ρ² and a decaying error. "
                        + "The amplitude is nonzero because Re(ρ) < 1. The finite-prefix "
                        + "Young inequality bounds the response energy by the input energy. "
                        + "The substitution x = exp(t) at U = N log 2 converts that input "
                        + "energy to the stated shell sum."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Scale()
    {
        var beta = F.Beta;
        var limit = F.Id("U");
        return F.Seq(Call(F.Id("K"), beta, limit), F.Eq,
            F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(limit), F.Sp,
            Call(F.Exp, F.Seq(F.Open, F.D(2), beta, F.Sp, F.Minus, F.D(1), F.Close, F.Id("t"))),
            F.Thin, F.Id("d"), F.Sp, F.Id("t"));
    }

    private static Formula LowerBound()
    {
        var rho = F.Rho;
        var re = Call(F.Re, rho);
        var c = F.Id("c");
        var cutoff = F.Id("N");
        var threshold = F.Seq(F.Id("N"), F.Underscore, F.Grp(F.D(0)));
        var shell = F.Id("k");
        return F.Seq(
            F.Forall, F.Sp, rho, F.Sp, F.InMacro, F.Sp, Field("C"), F.Comma, F.Sp,
            F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)), F.Sp, F.Leq, F.Sp, re,
            F.Sp, F.Lt, F.Sp, F.D(1), F.Sp, F.Land, F.Sp,
            Call(F.Zeta, rho), F.Eq, F.D(0), F.Sp, F.Implies, F.Sp,
            F.Exists, F.Sp, c, F.Sp, F.InMacro, F.Sp, Field("R"), F.Comma, F.Sp,
            F.D(0), F.Lt, c, F.Sp, F.Land, F.Sp,
            F.Open, F.Exists, F.Sp, threshold, F.Sp, F.InMacro, F.Sp, Field("N"), F.Comma, F.Sp,
            F.Forall, F.Sp, cutoff, F.Sp, F.InMacro, F.Sp, Field("N"), F.Comma, F.Sp,
            threshold, F.Sp, F.Leq, F.Sp, cutoff, F.Sp, F.Implies, F.Sp,
            c, F.Sp, Call(F.Id("K"), re, F.Seq(cutoff, F.Sp, F.Log, F.Sp, F.D(2))),
            F.Sp, F.Leq, F.Sp, F.Sum, F.Underscore,
            F.Grp(F.D(0), F.Sp, F.Leq, F.Sp, shell, F.Lt, cutoff),
            F.Sp, Call(F.Id("E"), shell), F.Close);
    }

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Call(Formula head, params Formula[] arguments) =>
        new Formula.Apply(head, [.. arguments]);
}
