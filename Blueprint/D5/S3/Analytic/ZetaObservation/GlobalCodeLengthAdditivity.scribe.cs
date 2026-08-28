using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class GlobalCodeLengthAdditivityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zeta sample's surprisal is the sum of its prime-coordinate code lengths.",
        H("Global Code Length Additivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-coordinate-code-length"),
                DeclarationHandle.Create(DeclarationPrefix + "primeCodeLength"),
                H("Prime-coordinate code length"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At prime p, exponent k has the geometric baseline minus log of one "
                        + "minus p to the power minus s, plus the occupied cost s k log p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("global-code-length-is-prime-additive"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "global_code_length_additive"),
                H("Global code length adds over prime coordinates"),
                StatementSource.FromAuthor(AdditivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive sampled natural, its negative log zeta mass is "
                            + "the convergent sum of the local code lengths over all primes.")),
                    Paragraph(Text(
                        "The common baseline is the logarithm of the Euler product. The "
                            + "occupied contribution is s log n by unique factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-sample-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "positive_sample_is_necessary"),
                H("The positive-sample condition is necessary"),
                StatementSource.FromAuthor(PositiveSampleNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At s equal to two and n equal to zero, the totalized negative log mass "
                        + "is zero, while the sum of the positive Euler baselines is positive."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula k = F.Id("k");
        Formula inversePower = new Formula.Power(p, F.Grp(F.Minus, s));
        Formula baseline = F.Seq(
            F.Minus,
            Log(F.Grp(F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, inversePower))));
        Formula occupied = F.Seq(s, F.Sp, k, F.Sp, Log(p));
        return F.Disp(new Formula.Relation(
            PrimeCodeLength(p, s, k),
            FormulaRelationOperator.Equal,
            F.Seq(baseline, F.Sp, F.Plus, F.Sp, occupied)));
    }

    private static Formula AdditivityFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula n = F.Id("n");
        Formula domain = And(
            new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s),
            new Formula.Relation(F.D(1), FormulaRelationOperator.LessThanOrEqual, n));
        Formula localSum = SumPrimes(
            p,
            PrimeCodeLength(p, s, PrimeValuation(p, n)));
        Formula equality = new Formula.Relation(
            F.Seq(F.Minus, Log(ZetaMass(s, n))),
            FormulaRelationOperator.Equal,
            localSum);
        return F.Disp(F.Seq(
            F.Forall, F.Sp, s, F.Comma, F.Sp, n, F.Comma, F.Sp,
            new Formula.Logic(domain, FormulaLogicOperator.Implies, equality)));
    }

    private static Formula PositiveSampleNecessaryFormula()
    {
        Formula p = F.Id("p");
        Formula localSum = SumPrimes(
            p,
            PrimeCodeLength(p, F.D(2), PrimeValuation(p, F.D(0))));
        return F.Disp(F.Seq(
            F.Minus, Log(ZetaMass(F.D(2), F.D(0))), F.Sp, F.Neq, F.Sp, localSum));
    }

    private static Formula PrimeCodeLength(Formula p, Formula s, Formula k) =>
        F.Seq(
            new Formula.Subscript(F.Id("ell"), F.Seq(p, F.Comma, s)),
            F.Open, k, F.Close);

    private static Formula PrimeValuation(Formula p, Formula n) =>
        F.Seq(new Formula.Subscript(F.Id("v"), p), F.Open, n, F.Close);

    private static Formula ZetaMass(Formula s, Formula n) =>
        F.Seq(new Formula.Subscript(F.Id("P"), s), F.Open, n, F.Close);

    private static Formula Log(Formula value) =>
        new Formula.Apply(F.Id("log"), [value]);

    private static Formula SumPrimes(Formula p, Formula term) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(p, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P"))),
            F.Sp, term);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
