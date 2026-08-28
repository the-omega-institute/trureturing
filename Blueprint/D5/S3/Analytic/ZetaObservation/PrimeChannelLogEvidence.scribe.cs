using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class PrimeChannelLogEvidenceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expected zeta log evidence is the summable total of its prime channels.",
        H("Prime-Channel Log-Evidence Additivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-channel-log-evidence-definition"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeChannelLogEvidence"),
                H("One prime channel supplies an expected log-likelihood ratio"),
                StatementSource.FromAuthor(LocalDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source law is the geometric prime-exponent marginal at s. Its "
                        + "expectation of the log likelihood ratio against parameter t is "
                        + "the evidence assigned to that channel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeta-family-log-evidence-definition"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zetaFamilyLogEvidence"),
                H("Global evidence is the zeta-law expected log-likelihood ratio"),
                StatementSource.FromAuthor(GlobalDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The global quantity uses the same real-valued log-likelihood "
                        + "expression on the complete zeta distribution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-channel-log-evidence-closed-form"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeChannelLogEvidence_eq"),
                H("A prime channel has the geometric KL closed form"),
                StatementSource.FromAuthor(LocalClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing the normalized geometric law separates its normalizer ratio "
                        + "from the expected exponent contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-family-log-evidence-closed-form"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zetaFamilyLogEvidence_eq"),
                H("Global evidence separates into energy and partition terms"),
                StatementSource.FromAuthor(GlobalClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The global likelihood ratio is affine in log n. Its expectation is "
                        + "therefore an energy difference plus a log-partition difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-channel-log-evidence-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "summable_primeChannelLogEvidence"),
                H("Valid zeta parameters make the channel family summable"),
                StatementSource.FromAuthor(SummabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Prime marginal entropy and min-entropy summability isolate a summable "
                        + "prime-energy family. The local closed form then proves absolute "
                        + "summability without an extra hidden premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-family-log-evidence-prime-sum"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zetaFamilyLogEvidence_eq_tsum_prime"),
                H("Total evidence is the sum of prime-channel evidence"),
                StatementSource.FromAuthor(AdditivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Euler log bridge and prime-energy bridge identify the two global "
                        + "closed-form terms with their summable prime-coordinate series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-zeta-parameters-have-zero-evidence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "equal_parameters_have_zero_evidence"),
                H("Equal parameters are indistinguishable"),
                StatementSource.FromAuthor(DiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At s equal to t, every likelihood ratio is one. Every channel, the "
                        + "global expectation, and the prime sum are all zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-zeta-parameters-have-positive-channel-evidence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeChannelLogEvidence_pos"),
                H("Every prime channel distinguishes unequal parameters"),
                StatementSource.FromAuthor(PositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A geometric channel reduces to a two-point mass split. Strict finite "
                        + "Gibbs positivity proves that its expected log evidence is positive "
                        + "whenever the two parameters differ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-prime-channels-strictly-accumulate"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "two_three_channels_strictly_accumulate"),
                H("Two positive channels strictly increase the evidence total"),
                StatementSource.FromAuthor(StrictAccumulationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the distinct prime channels two and three, both contributions are "
                        + "positive, so their sum is strictly larger than either one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parameter-disequality-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "parameter_disequality_is_necessary"),
                H("Disequality is necessary for strict evidence"),
                StatementSource.FromAuthor(DisequalityNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete diagonal choice s equals t equals two has zero evidence "
                        + "at prime two, ruling out strict positivity without disequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonsummable-prime-family-totalizes-to-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonsummable_prime_family_totalized"),
                H("A divergent bare tsum is totalized to zero"),
                StatementSource.FromAuthor(TotalizedDivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive reciprocal-prime family is not summable, while its bare "
                        + "real tsum is zero by totalization. This contrast explains why the "
                        + "main theorem first proves summability."))),
                DescribeRole.Theorem))));

    private static Formula LocalDefinitionFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula source = PrimeMass(s, p, k);
        Formula reference = PrimeMass(t, p, k);
        Formula term = F.Seq(
            source, F.Sp, F.Cdot, F.Sp,
            Log(new Formula.Fraction(source, reference)));
        return F.Disp(new Formula.Relation(
            LocalEvidence(s, t, p),
            FormulaRelationOperator.Equal,
            SumNaturals(k, term)));
    }

    private static Formula GlobalDefinitionFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula n = F.Id("n");
        Formula source = ZetaMass(s, n);
        Formula reference = ZetaMass(t, n);
        Formula term = F.Seq(
            source, F.Sp, F.Cdot, F.Sp,
            Log(new Formula.Fraction(source, reference)));
        return F.Disp(new Formula.Relation(
            GlobalEvidence(s, t),
            FormulaRelationOperator.Equal,
            SumNaturals(n, term)));
    }

    private static Formula LocalClosedFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula qs = PrimeActivation(s, p);
        Formula qt = PrimeActivation(t, p);
        Formula oneMinusQs = F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, qs);
        Formula oneMinusQt = F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, qt);
        Formula normalizer = Log(new Formula.Fraction(oneMinusQs, oneMinusQt));
        Formula energy = F.Seq(
            F.Grp(t, F.Sp, F.Minus, F.Sp, s), F.Sp, F.Cdot, F.Sp,
            Log(p), F.Sp, F.Cdot, F.Sp,
            new Formula.Fraction(qs, oneMinusQs));
        return F.Disp(new Formula.Relation(
            LocalEvidence(s, t, p),
            FormulaRelationOperator.Equal,
            F.Seq(normalizer, F.Sp, F.Plus, F.Sp, energy)));
    }

    private static Formula GlobalClosedFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula energy = F.Seq(
            F.Grp(t, F.Sp, F.Minus, F.Sp, s), F.Sp, F.Cdot, F.Sp,
            ExpectedLog(s));
        Formula partitionDifference = F.Seq(
            Log(Partition(t)), F.Sp, F.Minus, F.Sp, Log(Partition(s)));
        return F.Disp(new Formula.Relation(
            GlobalEvidence(s, t),
            FormulaRelationOperator.Equal,
            F.Seq(energy, F.Sp, F.Plus, F.Sp, partitionDifference)));
    }

    private static Formula SummabilityFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula premise = ParameterDomain(s, t);
        Formula conclusion = IsSummable(LocalEvidenceFamily(s, t));
        return F.Disp(new Formula.Logic(
            premise,
            FormulaLogicOperator.Implies,
            conclusion));
    }

    private static Formula AdditivityFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula equality = new Formula.Relation(
            GlobalEvidence(s, t),
            FormulaRelationOperator.Equal,
            SumPrimes(p, LocalEvidence(s, t, p)));
        return F.Disp(new Formula.Logic(
            ParameterDomain(s, t),
            FormulaLogicOperator.Implies,
            equality));
    }

    private static Formula DiagonalFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula localZero = F.Seq(
            F.Forall, F.Sp, p, F.Comma, F.Sp,
            new Formula.Relation(
                LocalEvidence(s, s, p),
                FormulaRelationOperator.Equal,
                F.D(0)));
        Formula globalZero = new Formula.Relation(
            GlobalEvidence(s, s),
            FormulaRelationOperator.Equal,
            F.D(0));
        Formula sumZero = new Formula.Relation(
            SumPrimes(p, LocalEvidence(s, s, p)),
            FormulaRelationOperator.Equal,
            F.D(0));
        return F.Disp(And(localZero, And(globalZero, sumZero)));
    }

    private static Formula PositivityFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula distinct = new Formula.Relation(
            s, FormulaRelationOperator.NotEqual, t);
        Formula positive = F.Seq(
            F.Forall, F.Sp, p, F.Comma, F.Sp,
            new Formula.Relation(
                F.D(0),
                FormulaRelationOperator.LessThan,
                LocalEvidence(s, t, p)));
        return F.Disp(new Formula.Logic(
            And(ParameterDomain(s, t), distinct),
            FormulaLogicOperator.Implies,
            positive));
    }

    private static Formula StrictAccumulationFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula e2 = LocalEvidence(s, t, F.D(2));
        Formula e3 = LocalEvidence(s, t, F.D(3));
        Formula sum = F.Seq(e2, F.Sp, F.Plus, F.Sp, e3);
        Formula body = And(
            Positive(e2),
            And(
                Positive(e3),
                And(
                    new Formula.Relation(
                        e2, FormulaRelationOperator.LessThan, sum),
                    new Formula.Relation(
                        e3, FormulaRelationOperator.LessThan, sum))));
        Formula distinct = new Formula.Relation(
            s, FormulaRelationOperator.NotEqual, t);
        return F.Disp(new Formula.Logic(
            And(ParameterDomain(s, t), distinct),
            FormulaLogicOperator.Implies,
            body));
    }

    private static Formula DisequalityNecessaryFormula()
    {
        Formula local = LocalEvidence(F.D(2), F.D(2), F.D(2));
        return F.Disp(Not(Positive(local)));
    }

    private static Formula TotalizedDivergenceFormula()
    {
        Formula p = F.Id("p");
        Formula reciprocal = new Formula.Fraction(F.D(1), p);
        Formula family = F.Seq(p, F.Mapsto, F.Sp, reciprocal);
        Formula sumZero = new Formula.Relation(
            SumPrimes(p, reciprocal),
            FormulaRelationOperator.Equal,
            F.D(0));
        return F.Disp(And(Not(IsSummable(family)), sumZero));
    }

    private static Formula LocalEvidence(Formula s, Formula t, Formula p) =>
        new Formula.Apply(F.Id("E"), [s, t, p]);

    private static Formula GlobalEvidence(Formula s, Formula t) =>
        new Formula.Apply(F.Id("ZetaEvidence"), [s, t]);

    private static Formula PrimeMass(Formula s, Formula p, Formula k) =>
        new Formula.Apply(F.Id("PrimeMass"), [s, p, k]);

    private static Formula ZetaMass(Formula s, Formula n) =>
        new Formula.Apply(F.Id("ZetaMass"), [s, n]);

    private static Formula PrimeActivation(Formula s, Formula p) =>
        new Formula.Power(p, F.Grp(F.Minus, s));

    private static Formula ExpectedLog(Formula s) =>
        new Formula.Apply(F.Id("ExpectedLog"), [s]);

    private static Formula Partition(Formula s) =>
        new Formula.Apply(F.Id("Z"), [s]);

    private static Formula Log(Formula value) =>
        new Formula.Apply(F.Id("log"), [value]);

    private static Formula SumNaturals(Formula index, Formula term) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(index, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N"))),
            F.Sp, term);

    private static Formula SumPrimes(Formula prime, Formula term) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(prime, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P"))),
            F.Sp, term);

    private static Formula LocalEvidenceFamily(Formula s, Formula t)
    {
        Formula p = F.Id("p");
        return F.Seq(p, F.Mapsto, F.Sp, LocalEvidence(s, t, p));
    }

    private static Formula ParameterDomain(Formula s, Formula t) =>
        And(
            new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s),
            new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, t));

    private static Formula IsSummable(Formula family) =>
        new Formula.Apply(F.Id("Summable"), [family]);

    private static Formula Positive(Formula value) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, value);

    private static Formula Not(Formula value) =>
        F.Seq(F.Neg, F.Sp, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
