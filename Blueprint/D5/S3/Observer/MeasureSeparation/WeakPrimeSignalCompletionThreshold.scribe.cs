using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class WeakPrimeSignalCompletionThresholdDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak prime signals separate exactly at exponent one half.",
        H("The Weak Prime Signal Completion Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weak-prime-signal-family"),
                DeclarationHandle.Create(DeclarationPrefix + "weakPrimeSignal"),
                H("A weak prime signal is an amplitude times an inverse power"),
                StatementSource.FromAuthor(SignalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signal attached to a prime is a fixed amplitude times the "
                        + "first-event mass at the given exponent. Naming the family keeps "
                        + "the energy sum, the threshold, and the degeneracy audit tied to "
                        + "one definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signal-energy-is-quadratic"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "weak_prime_signal_quadratic_energy"),
                H("Signal energy is the amplitude squared times the prime power sum"),
                StatementSource.FromAuthor(EnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing the squared signal over the primes factors the amplitude out "
                        + "of the series, leaving the prime inverse-power sum at twice the "
                        + "exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("energy-diverges-at-and-below-one-half"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "weak_prime_signal_energy_not_summable_iff_half_le"),
                H("Energy diverges exactly at and below one half"),
                StatementSource.FromAuthor(DivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero amplitude the energy series fails to converge precisely "
                        + "when the exponent is at most one half. The boundary value itself "
                        + "lies on the divergent side."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weak-signal-completion-dichotomy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "weak_prime_signal_completion_dichotomy"),
                H("The completion dichotomy at exponent one half"),
                StatementSource.FromAuthor(DichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the named signal dichotomy hypothesis, the two product laws "
                        + "are mutually singular exactly when the exponent is at most one "
                        + "half, and mutually absolutely continuous exactly when it exceeds "
                        + "one half.")),
                    Paragraph(Text(
                        "The dichotomy hypothesis stands for the Kakutani product-measure "
                        + "criterion, which pinned mathlib does not provide; it is carried "
                        + "as an explicit named premise rather than assumed silently."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-amplitude-is-necessary"),
                DeclarationHandle.Create(DeclarationPrefix + "nonzero_amplitude_is_necessary"),
                H("A zero amplitude collapses the threshold"),
                StatementSource.FromAuthor(ZeroAmplitudeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With zero amplitude every signal vanishes and the energy converges for "
                        + "every exponent, so the nonzero-amplitude hypothesis cannot be "
                        + "dropped."))),
                DescribeRole.Theorem))));

    private static Formula Signal(Formula amplitude, Formula exponent, Formula prime) =>
        new Formula.Apply(F.Id("delta"), [amplitude, exponent, prime]);

    private static Formula Half() => new Formula.Fraction(D(1), D(2));

    private static Formula SignalFormula()
    {
        Formula amplitude = F.Id("c");
        Formula exponent = F.Id("alpha");
        Formula prime = F.Id("p");
        return Disp(new Formula.Relation(
            Signal(amplitude, exponent, prime),
            FormulaRelationOperator.Equal,
            Seq(amplitude, Cdot, Sp,
                new Formula.Power(prime, Grp(Seq(Minus, exponent))))));
    }

    private static Formula EnergyFormula()
    {
        Formula amplitude = F.Id("c");
        Formula exponent = F.Id("alpha");
        Formula prime = F.Id("p");
        Formula energy = new Formula.Apply(F.Id("E"), [amplitude, exponent]);
        Formula right = Seq(
            new Formula.Power(amplitude, D(2)), Sp,
            Sum, Underscore, Grp(prime), Sp,
            new Formula.Power(prime, Grp(Seq(Minus, D(2), exponent))));
        return Disp(new Formula.Relation(
            energy, FormulaRelationOperator.Equal, right));
    }

    private static Formula DivergenceFormula()
    {
        Formula exponent = F.Id("alpha");
        return Disp(new Formula.Logic(
            Seq(Neg, Sp, new Formula.Apply(F.Id("Summable"), [F.Id("energy")])),
            FormulaLogicOperator.Iff,
            new Formula.Relation(
                exponent, FormulaRelationOperator.LessThanOrEqual, Half())));
    }

    private static Formula DichotomyFormula()
    {
        Formula exponent = F.Id("alpha");
        Formula lawP = F.Id("P");
        Formula lawQ = F.Id("Q");
        Formula singular = new Formula.Logic(
            Seq(lawP, Sp, Perp, Sp, lawQ),
            FormulaLogicOperator.Iff,
            new Formula.Relation(
                exponent, FormulaRelationOperator.LessThanOrEqual, Half()));
        Formula equivalent = new Formula.Logic(
            new Formula.Apply(F.Id("Equivalent"), [lawP, lawQ]),
            FormulaLogicOperator.Iff,
            new Formula.Relation(
                Half(), FormulaRelationOperator.LessThan, exponent));
        return Disp(new Formula.Logic(
            singular, FormulaLogicOperator.And, equivalent));
    }

    private static Formula ZeroAmplitudeFormula()
    {
        Formula exponent = F.Id("alpha");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Relation(
                Signal(D(0), exponent, prime),
                FormulaRelationOperator.Equal,
                D(0))));
    }
}
