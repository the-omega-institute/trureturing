using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class FinitePrimeEvenDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty finite prime layer detects every nonzero mirror offset.",
        H("Finite Prime Even Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-mirror-mean-is-hyperbolic-cosine"),
                DeclarationHandle.Create(Prefix + "prime_mirror_mean_eq_cosh"),
                H("The mirror-prime mean is a hyperbolic cosine"),
                StatementSource.FromAuthor(MirrorMeanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p and real offset delta, the arithmetic mean of the "
                        + "positive and negative real prime powers is cosh(delta log p)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prime-even-defect"),
                DeclarationHandle.Create(Prefix + "finitePrimeEvenDefect"),
                H("Finite prime even defect"),
                StatementSource.FromAuthor(DefectDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defect doubles the finite sum of reciprocal-prime-weighted excesses "
                        + "of cosh(delta log p) above one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("each-prime-defect-term-is-nonnegative"),
                DeclarationHandle.Create(Prefix + "prime_even_defect_term_nonneg"),
                H("Each prime defect term is nonnegative"),
                StatementSource.FromAuthor(TermNonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib gives cosh x at least one, and every prime is positive, so "
                        + "division by p preserves nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-offset-has-positive-finite-prime-defect"),
                DeclarationHandle.Create(Prefix + "finite_prime_even_defect_pos"),
                H("A nonzero offset has positive finite-prime defect"),
                StatementSource.FromAuthor(PositiveDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose a prime from the nonempty layer. Its logarithm is nonzero, so a "
                            + "nonzero delta makes delta log p nonzero and the strict cosh "
                            + "criterion makes that summand positive.")),
                    Paragraph(Text(
                        "All remaining summands are nonnegative; hence the complete finite sum "
                            + "and its positive factor two are strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prime-defect-zero-iff-offset-zero"),
                DeclarationHandle.Create(Prefix + "finite_prime_even_defect_eq_zero_iff"),
                H("The finite-prime defect vanishes exactly at zero offset"),
                StatementSource.FromAuthor(ZeroCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonempty finite set of primes, a nonzero offset has positive "
                            + "defect by the preceding theorem, while substitution of delta zero "
                            + "makes every hyperbolic-cosine excess vanish.")),
                    Paragraph(Text(
                        "This closes the exact finite-layer detection claim. The source's later "
                            + "informal small-offset and prime-number-scale asymptotic discussion "
                            + "is not asserted by this declaration."))),
                DescribeRole.Theorem))));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula PrimeNumbers() =>
        Seq(Operatorname, Grp(F.Id("NatPrimes")));

    private static Formula PrimeFinset() =>
        Call("Finset", PrimeNumbers());

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Log(Formula value) =>
        Call("log", value);

    private static Formula Cosh(Formula value) =>
        Call("cosh", value);

    private static Formula Defect(Formula primes, Formula delta) =>
        Call("finitePrimeEvenDefect", primes, delta);

    private static Formula MirrorMeanFormula()
    {
        Formula prime = F.Id("p");
        Formula delta = F.Id("delta");
        Formula mean = Fraction(
            Seq(Power(prime, delta), Sp, Plus, Sp,
                Power(prime, Seq(Minus, delta))),
            D(2));
        Formula argument = Seq(delta, Sp, Cdot, Sp, Log(prime));

        return Disp(Seq(
            Forall, Sp, prime, Colon, Sp, PrimeNumbers(), Comma, Sp,
            delta, Colon, Sp, RealNumbers(), Comma, RowBreak, Grp(),
            mean, Sp, Eq, Sp, Cosh(argument), Dot));
    }

    private static Formula DefectDefinitionFormula()
    {
        Formula primes = F.Id("P");
        Formula delta = F.Id("delta");
        Formula prime = F.Id("p");
        Formula argument = Seq(delta, Sp, Cdot, Sp, Log(prime));
        Formula summand = Fraction(
            Seq(Cosh(argument), Sp, Minus, Sp, D(1)),
            prime);
        Formula sum = Seq(
            Sum, Underscore, Grp(Seq(prime, Sp, InMacro, Sp, primes)), Sp,
            summand);

        return Disp(Seq(
            Forall, Sp, primes, Colon, Sp, PrimeFinset(), Comma, Sp,
            delta, Colon, Sp, RealNumbers(), Comma, RowBreak, Grp(),
            Defect(primes, delta), Sp, Eq, Sp, D(2), Sp, Cdot, Sp, sum, Dot));
    }

    private static Formula TermNonnegativeFormula()
    {
        Formula prime = F.Id("p");
        Formula delta = F.Id("delta");
        Formula argument = Seq(delta, Sp, Cdot, Sp, Log(prime));
        Formula term = Fraction(
            Seq(Cosh(argument), Sp, Minus, Sp, D(1)),
            prime);

        return Disp(Seq(
            Forall, Sp, prime, Colon, Sp, PrimeNumbers(), Comma, Sp,
            delta, Colon, Sp, RealNumbers(), Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, term, Dot));
    }

    private static Formula PositiveDefectFormula()
    {
        Formula primes = F.Id("P");
        Formula delta = F.Id("delta");
        Formula hypotheses = Seq(
            Call("Nonempty", primes), Sp, Land, Sp,
            delta, Sp, Neq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, primes, Colon, Sp, PrimeFinset(), Comma, Sp,
            delta, Colon, Sp, RealNumbers(), Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, Defect(primes, delta), Dot));
    }

    private static Formula ZeroCriterionFormula()
    {
        Formula primes = F.Id("P");
        Formula delta = F.Id("delta");
        Formula conclusion = Seq(
            Defect(primes, delta), Sp, Eq, Sp, D(0), Sp,
            Leftrightarrow, Sp, delta, Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, primes, Colon, Sp, PrimeFinset(), Comma, Sp,
            delta, Colon, Sp, RealNumbers(), Comma, RowBreak, Grp(),
            Call("Nonempty", primes), Sp, Rightarrow, Sp,
            conclusion, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
