using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class GlobalPrimeExponentRealizabilityDocument
    : IScribeDocumentDefinition
{
    private const string LeanPath =
        "D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent geometric prime exponents come from one positive-integer law "
            + "exactly above the zeta threshold, and that law is unique.",
        H("Global Prime-Exponent Realizability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometric-prime-mass"),
                DeclarationHandle.Create(LeanPath + "geometricPrimeMass"),
                H("Geometric prime mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the prescribed zero-start geometric mass at a prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-exponent-code"),
                DeclarationHandle.Create(LeanPath + "primeExponentCode"),
                H("Prime-exponent code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This function records every prime exponent in a natural number."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realizes-prime-exponent-law"),
                DeclarationHandle.Create(LeanPath + "RealizesPrimeExponentLaw"),
                H("Realization of the prime-exponent law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A realization has no mass at zero, independent exponent coordinates, "
                        + "and every prescribed geometric marginal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-integer-support-is-necessary"),
                DeclarationHandle.Create(
                    LeanPath + "positive_integer_support_is_necessary"),
                H("Positive support is necessary for exponent-code uniqueness"),
                StatementSource.FromAuthor(PositiveSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Point masses at zero and one are distinct but have the same complete "
                        + "prime-exponent code, so excluding zero is necessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-prime-mass-at-zero"),
                DeclarationHandle.Create(LeanPath + "geometric_prime_mass_zero"),
                H("The zero-exponent mass"),
                StatementSource.FromAuthor(ZeroMassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent zero the geometric factor is one, leaving one minus "
                        + "the prime activation probability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-realizes-prime-exponent-law"),
                DeclarationHandle.Create(
                    LeanPath + "zeta_realizes_prime_exponent_law"),
                H("The zeta law realizes the exponent family"),
                StatementSource.FromAuthor(ZetaRealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above one, the repository zeta distribution has independent prime "
                        + "factorizations and the required geometric marginals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global-prime-exponent-realizable-iff"),
                DeclarationHandle.Create(
                    LeanPath + "global_prime_exponent_realizable_iff"),
                H("Global realizability has threshold one"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Existence above one is supplied by the zeta distribution.")),
                    Paragraph(Text(
                        "At positive exponents at most one, the canonical product gives "
                            + "finite-support profiles measure zero by the prime-series "
                            + "threshold and Borel-Cantelli. Nonpositive exponents already "
                            + "make a prescribed prime marginal have total mass zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-exponent-realization-unique"),
                DeclarationHandle.Create(
                    LeanPath + "prime_exponent_realization_unique"),
                H("The realization is unique"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Independence identifies the joint exponent product law. Unique prime "
                        + "factorization recovers each positive natural-number atom."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-exponent-realization-mass"),
                DeclarationHandle.Create(
                    LeanPath + "prime_exponent_realization_mass"),
                H("The unique mass is the normalized zeta weight"),
                StatementSource.FromAuthor(MassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every atom equals its power-law weight divided by the real zeta "
                        + "partition function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-exponent-not-realizable"),
                DeclarationHandle.Create(LeanPath + "zero_exponent_not_realizable"),
                H("Exponent zero is not realizable"),
                StatementSource.FromAuthor(ZeroNonrealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold theorem rules out the concrete exponent zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-exponent-not-realizable"),
                DeclarationHandle.Create(
                    LeanPath + "critical_exponent_not_realizable"),
                H("The critical exponent is not realizable"),
                StatementSource.FromAuthor(CriticalNonrealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold theorem also rules out the critical exponent one."))),
                DescribeRole.Theorem))));

    private static Formula PositiveSupportFormula() => Disp(Seq(
        Call("map", F.Id("V"), Seq(Delta, Underscore, D(0))), Eq,
        Call("map", F.Id("V"), Seq(Delta, Underscore, D(1))), Sp,
        Land, Sp, Delta, Underscore, D(0), Neq, Delta, Underscore, D(1), Dot));

    private static Formula ZeroMassFormula() => Disp(Seq(
        F.Id("g"), Underscore, Grp(F.Id("s"), Comma, F.Id("p")), Open, D(0), Close,
        Eq, D(1), Minus, F.Id("p"), Caret, Grp(Minus, F.Id("s")), Dot));

    private static Formula ZetaRealizationFormula()
    {
        Formula s = F.Id("s");
        Formula zetaLaw = Seq(Zeta, Underscore, Grp(s));
        return Disp(Seq(
            D(1), Lt, s, Sp, Rightarrow, Sp,
            Call("Realizes", s, zetaLaw), Dot));
    }

    private static Formula ThresholdFormula() => Disp(Seq(
        Open, Exists, Sp, F.Id("q"), Comma, Sp,
        Call("Realizes", F.Id("s"), F.Id("q")), Close,
        Sp, Leftrightarrow, Sp, D(1), Lt, F.Id("s"), Dot));

    private static Formula UniquenessFormula()
    {
        Formula s = F.Id("s");
        Formula q = F.Id("q");
        Formula zetaLaw = Seq(Zeta, Underscore, Grp(s));
        return Disp(Seq(
            D(1), Lt, s, Sp, Land, Sp, Call("Realizes", s, q),
            Sp, Rightarrow, Sp, q, Eq, zetaLaw, Dot));
    }

    private static Formula MassFormula() => Disp(Seq(
        F.Id("q"), Open, F.Id("n"), Close, Eq,
        Frac, Grp(F.Id("n"), Caret, Grp(Minus, F.Id("s"))),
        Grp(Zeta, Open, F.Id("s"), Close), Dot));

    private static Formula ZeroNonrealizationFormula() => Disp(new Formula.Not(Seq(
        Exists, Sp, F.Id("q"), Comma, Sp,
        Call("Realizes", D(0), F.Id("q")))));

    private static Formula CriticalNonrealizationFormula() => Disp(new Formula.Not(Seq(
        Exists, Sp, F.Id("q"), Comma, Sp,
        Call("Realizes", D(1), F.Id("q")))));
}
