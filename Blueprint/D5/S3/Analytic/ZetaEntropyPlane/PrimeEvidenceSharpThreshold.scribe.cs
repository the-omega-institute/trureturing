using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeEvidenceSharpThresholdDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-indexed positive evidence is summable exactly above exponent one.",
        H("The Sharp Threshold for Positive Prime Evidence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-evidence-family"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence"),
                H("Prime evidence is an inverse power"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real exponent s and a prime p, prime evidence is p raised to "
                        + "minus s. Naming this family keeps the convergence boundary, its "
                        + "specializations, and the degeneration audit tied to one definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-evidence-is-strictly-positive"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_pos"),
                H("Every prime contributes positive evidence"),
                StatementSource.FromAuthor(PositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime is a positive real base, so its real power is strictly "
                        + "positive for every exponent, including zero and negative exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-evidence-is-summable-above-one"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_summable"),
                H("Prime evidence is summable above one"),
                StatementSource.FromAuthor(SummableAboveOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural-number inverse-power series is summable for s greater than "
                        + "one. Restricting that family along the injective prime subtype "
                        + "preserves summability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-square-prime-evidence-is-summable"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_two_summable"),
                H("Inverse-square prime evidence is summable"),
                StatementSource.FromAuthor(Disp(IsSummable(D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exponent two lies strictly above the threshold, so the positive family "
                        + "p to the power minus two has a finite sum over all primes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-reciprocal-evidence-is-not-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeEvidence_one_not_summable"),
                H("Prime reciprocal evidence diverges"),
                StatementSource.FromAuthor(Disp(Not(IsSummable(D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent one the family is exactly the reciprocal-prime series. "
                        + "Euler's divergence theorem, as provided by pinned mathlib, makes "
                        + "this boundary family nonsummable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-evidence-has-exact-threshold-one"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeEvidence_summable_iff_one_lt"),
                H("Exponent one is the exact summability threshold"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime power family is summable if and only if its exponent is "
                        + "strictly greater than one. Thus the convergence assumption cannot "
                        + "be weakened merely to positivity of the exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-evidence-at-and-below-one-diverges"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_at_most_one"),
                H("Positive prime evidence diverges at and below one"),
                StatementSource.FromAuthor(AtMostOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every s at most one, all prime terms remain strictly positive while "
                        + "the family is nonsummable. This includes s equal to zero and every "
                        + "negative exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-exponent-prime-evidence-is-constant-and-divergent"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_zero"),
                H("Zero exponent gives a constant divergent family"),
                StatementSource.FromAuthor(ZeroExponentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent zero every prime contributes exactly one. The resulting "
                        + "constant family over the infinite prime subtype is nonsummable, "
                        + "making the relevant trivial-map degeneration explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smallest-prime-inverse-square-evidence"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_two_at_two"),
                H("The smallest-prime evidence is one quarter"),
                StatementSource.FromAuthor(SmallestPrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent two, the smallest prime contributes two to the power minus "
                        + "two, which is exactly one quarter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-exponent-does-not-imply-summability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "positive_exponent_is_insufficient"),
                H("A positive exponent does not ensure summability"),
                StatementSource.FromAuthor(PositiveInsufficientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete exponent s equal to one is positive and every prime term is "
                        + "positive, yet the prime-indexed family diverges. This is the named "
                        + "counterexample showing why the strict threshold is necessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-prime-evidence-realizes-both-sides"),
                DeclarationHandle.Create(DeclarationPrefix + "primeEvidence_sharp_threshold"),
                H("One family realizes both sides of the sharp threshold"),
                StatementSource.FromAuthor(SharpThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Within the same prime-indexed evidence family, exponent two gives "
                        + "strictly positive summable evidence while exponent one gives "
                        + "strictly positive nonsummable evidence."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        Formula inversePower = new Formula.Power(prime, Grp(Seq(Minus, exponent)));
        return Disp(new Formula.Relation(
            Evidence(exponent, prime),
            FormulaRelationOperator.Equal,
            inversePower));
    }

    private static Formula PositiveFormula()
    {
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp, prime, Comma, Sp,
            D(0), Sp, Lt, Sp, Evidence(exponent, prime)));
    }

    private static Formula SummableAboveOneFormula()
    {
        Formula exponent = F.Id("s");
        Formula premise = new Formula.Relation(
            D(1), FormulaRelationOperator.LessThan, exponent);
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                premise,
                FormulaLogicOperator.Implies,
                IsSummable(exponent))));
    }

    private static Formula ThresholdFormula()
    {
        Formula exponent = F.Id("s");
        Formula bound = new Formula.Relation(
            D(1), FormulaRelationOperator.LessThan, exponent);
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                IsSummable(exponent),
                FormulaLogicOperator.Iff,
                bound)));
    }

    private static Formula AtMostOneFormula()
    {
        Formula exponent = F.Id("s");
        Formula bound = new Formula.Relation(
            exponent, FormulaRelationOperator.LessThanOrEqual, D(1));
        Formula conclusion = And(PositiveAt(exponent), Not(IsSummable(exponent)));
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(bound, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula SmallestPrimeFormula() =>
        Disp(new Formula.Relation(
            Evidence(D(2), D(2)),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(D(1), D(4))));

    private static Formula ZeroExponentFormula()
    {
        Formula prime = F.Id("p");
        Formula constant = Seq(
            Forall, Sp, prime, Comma, Sp,
            new Formula.Relation(
                Evidence(D(0), prime),
                FormulaRelationOperator.Equal,
                D(1)));
        return Disp(And(constant, Not(IsSummable(D(0)))));
    }

    private static Formula PositiveInsufficientFormula()
    {
        Formula exponent = F.Id("s");
        Formula exponentPositive = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThan, exponent);
        Formula body = And(
            exponentPositive,
            And(PositiveAt(exponent), Not(IsSummable(exponent))));
        return Disp(Seq(Exists, Sp, exponent, Comma, Sp, body));
    }

    private static Formula SharpThresholdFormula() =>
        Disp(And(
            PositiveAt(D(2)),
            And(
                IsSummable(D(2)),
                And(PositiveAt(D(1)), Not(IsSummable(D(1)))))));

    private static Formula Evidence(Formula exponent, Formula prime) =>
        Seq(new Formula.Subscript(F.Id("e"), exponent), Open, prime, Close);

    private static Formula EvidenceFamily(Formula exponent) =>
        new Formula.Subscript(F.Id("e"), exponent);

    private static Formula IsSummable(Formula exponent) =>
        new Formula.Apply(F.Id("Summable"), [EvidenceFamily(exponent)]);

    private static Formula PositiveAt(Formula exponent)
    {
        Formula prime = F.Id("p");
        return Seq(
            Forall, Sp, prime, Comma, Sp,
            D(0), Sp, Lt, Sp, Evidence(exponent, prime));
    }

    private static Formula Not(Formula formula) =>
        Seq(Neg, Sp, formula);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
