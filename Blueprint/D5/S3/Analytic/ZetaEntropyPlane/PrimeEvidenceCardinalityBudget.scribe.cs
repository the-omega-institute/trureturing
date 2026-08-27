using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeEvidenceCardinalityBudgetDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime evidence budgets are not controlled by the number of selected primes.",
        H("Evidence Budget Is a Sum, Not a Coordinate Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-evidence-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "finiteEvidenceBudget"),
                H("Finite evidence budget"),
                StatementSource.FromAuthor(FiniteEvidenceBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The budget of a finite selection is the sum of its evidence values. "
                        + "This named definition is shared by the core and every audit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("empty-selection-budget"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_evidence_budget_empty"),
                H("Empty selections have zero budget"),
                StatementSource.FromAuthor(EmptySelectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty finite sum is zero for every index type and evidence family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-index-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "empty_index_budget_zero"),
                H("The empty index type has zero budget"),
                StatementSource.FromAuthor(EmptyIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finite selection from Empty is empty, so every such budget is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-evidence-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "singleton_evidence_budget"),
                H("A singleton budget is its evidence value"),
                StatementSource.FromAuthor(SingletonBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-coordinate selection contributes exactly one summand."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-evidence-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "identity_evidence_budget"),
                H("Identity evidence gives the ordinary sum"),
                StatementSource.FromAuthor(IdentityBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity-map audit reduces the named budget to an ordinary sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-budget-cardinality-formula"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_evidence_budget_eq_card_mul"),
                H("Constant evidence is cardinality times value"),
                StatementSource.FromAuthor(ConstantBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every coordinate has value c, the budget is the set size times c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-cardinality-constant-budget"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "equal_cardinality_determines_constant_budget"),
                H("Cardinality determines every constant budget"),
                StatementSource.FromAuthor(EqualCardConstantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal cardinalities do determine equal sums under the constant-family "
                        + "restriction. This is the required contrast to the core theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-evidence-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "zero_evidence_budget"),
                H("Zero evidence has zero budget"),
                StatementSource.FromAuthor(ZeroBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-family specialization is zero for every finite selection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-index-budget"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "singleton_index_budget_eq_card_mul"),
                H("Every Unit-indexed budget is cardinality-determined"),
                StatementSource.FromAuthor(SingletonIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every function on Unit is constant, so its budget is size times its "
                        + "unique value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-one-prime-evidence"),
                DeclarationHandle.Create(DeclarationPrefix + "prime_evidence_negative_one"),
                H("Negative-one evidence is the prime value"),
                StatementSource.FromAuthor(NegativeOneEvidenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent minus one, the imported inverse-power family becomes p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-cardinality-unbounded-gap"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "equal_cardinality_prime_budget_gap_unbounded"),
                H("Equal-cardinality prime budgets have unbounded gaps"),
                StatementSource.FromAuthor(UnboundedGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real bound, two singleton prime sets have a budget gap above "
                        + "that bound at exponent minus one. Their common cardinality is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-exponent-budget-cardinality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_exponent_prime_budget_eq_card"),
                H("Zero-exponent prime budget equals cardinality"),
                StatementSource.FromAuthor(ZeroExponentCardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent zero every prime contributes one, so the sum is the size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-cardinality-zero-exponent-budget"),
                DeclarationHandle.Create(DeclarationPrefix
                    + "equal_cardinality_determines_zero_exponent_prime_budget"),
                H("Cardinality determines zero-exponent prime budgets"),
                StatementSource.FromAuthor(EqualCardZeroExponentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported prime family itself realizes the constant-family contrast "
                        + "at exponent zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-cardinality-hypothesis-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "equal_cardinality_hypothesis_is_necessary"),
                H("The equal-cardinality premise is necessary"),
                StatementSource.FromAuthor(CardinalityPremiseNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty prime set and the singleton containing two have unequal "
                        + "zero-exponent budgets. Dropping equal cardinality breaks the "
                        + "contrast."))),
                DescribeRole.Theorem))));

    private static Formula FiniteEvidenceBudgetFormula()
    {
        Formula evidence = F.Id("e");
        Formula indices = F.Id("J");
        Formula index = F.Id("i");
        Formula sum = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indices), Sp,
            new Formula.Apply(evidence, [index]));
        return Disp(Equal(Budget(evidence, indices), sum));
    }

    private static Formula EmptySelectionFormula()
    {
        Formula evidence = F.Id("e");
        return Disp(Seq(
            Forall, Sp, evidence, Comma, Sp,
            Equal(Budget(evidence, Emptyset), D(0))));
    }

    private static Formula EmptyIndexFormula()
    {
        Formula evidence = F.Id("e");
        Formula indices = F.Id("J");
        return Disp(Seq(
            Forall, Sp, evidence, Colon, Sp, F.Id("EmptyEvidence"), Comma, Sp,
            indices, Colon, Sp, F.Id("EmptyFinsets"), Comma, Sp,
            Equal(Budget(evidence, indices), D(0))));
    }

    private static Formula SingletonBudgetFormula()
    {
        Formula evidence = F.Id("e");
        Formula index = F.Id("i");
        return Disp(Seq(
            Forall, Sp, evidence, Comma, Sp, index, Comma, Sp,
            Equal(Budget(evidence, SingletonSet(index)),
                new Formula.Apply(evidence, [index]))));
    }

    private static Formula IdentityBudgetFormula()
    {
        Formula indices = F.Id("J");
        Formula index = F.Id("x");
        Formula sum = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indices), Sp, index);
        return Disp(Seq(
            Forall, Sp, indices, Comma, Sp,
            Equal(Budget(F.Id("id"), indices), sum)));
    }

    private static Formula ConstantBudgetFormula()
    {
        Formula value = F.Id("c");
        Formula indices = F.Id("J");
        return Disp(Seq(
            Forall, Sp, value, Comma, Sp, indices, Comma, Sp,
            Equal(
                Budget(ConstantFamily(value), indices),
                new Formula.Binary(
                    Card(indices), FormulaBinaryOperator.Multiply, value))));
    }

    private static Formula EqualCardConstantFormula()
    {
        Formula value = F.Id("c");
        Formula left = F.Id("J1");
        Formula right = F.Id("J2");
        Formula sameCard = Equal(Card(left), Card(right));
        Formula sameBudget = Equal(
            Budget(ConstantFamily(value), left),
            Budget(ConstantFamily(value), right));
        return Disp(Seq(
            Forall, Sp, value, Comma, Sp, left, Comma, Sp, right, Comma, Sp,
            new Formula.Logic(sameCard, FormulaLogicOperator.Implies, sameBudget)));
    }

    private static Formula ZeroBudgetFormula()
    {
        Formula indices = F.Id("J");
        return Disp(Seq(
            Forall, Sp, indices, Comma, Sp,
            Equal(Budget(ConstantFamily(D(0)), indices), D(0))));
    }

    private static Formula SingletonIndexFormula()
    {
        Formula evidence = F.Id("e");
        Formula indices = F.Id("J");
        Formula value = new Formula.Apply(evidence, [F.Id("unit")]);
        return Disp(Seq(
            Forall, Sp, evidence, Colon, Sp, F.Id("UnitEvidence"), Comma, Sp,
            indices, Colon, Sp, F.Id("UnitFinsets"), Comma, Sp,
            Equal(
                Budget(evidence, indices),
                new Formula.Binary(
                    Card(indices), FormulaBinaryOperator.Multiply, value))));
    }

    private static Formula NegativeOneEvidenceFormula()
    {
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, prime, Colon, Sp, F.Id("Primes"), Comma, Sp,
            Equal(PrimeEvidence(NegativeOne(), prime), prime)));
    }

    private static Formula UnboundedGapFormula()
    {
        Formula bound = F.Id("M");
        Formula left = F.Id("J1");
        Formula right = F.Id("J2");
        Formula evidence = PrimeEvidenceFamily(NegativeOne());
        Formula sameCard = Equal(Card(left), Card(right));
        Formula singletonCard = Equal(Card(left), D(1));
        Formula gap = Seq(Budget(evidence, right), Sp, Minus, Sp, Budget(evidence, left));
        Formula exceeds = new Formula.Relation(
            bound, FormulaRelationOperator.LessThan, gap);
        return Disp(Seq(
            Forall, Sp, bound, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, F.Id("PrimeFinsets"), Comma,
            Sp, And(sameCard, And(singletonCard, exceeds))));
    }

    private static Formula ZeroExponentCardFormula()
    {
        Formula indices = F.Id("J");
        return Disp(Seq(
            Forall, Sp, indices, Colon, Sp, F.Id("PrimeFinsets"), Comma, Sp,
            Equal(Budget(PrimeEvidenceFamily(D(0)), indices), Card(indices))));
    }

    private static Formula EqualCardZeroExponentFormula()
    {
        Formula left = F.Id("J1");
        Formula right = F.Id("J2");
        Formula sameCard = Equal(Card(left), Card(right));
        Formula sameBudget = Equal(
            Budget(PrimeEvidenceFamily(D(0)), left),
            Budget(PrimeEvidenceFamily(D(0)), right));
        return Disp(Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, F.Id("PrimeFinsets"),
            Comma, Sp,
            new Formula.Logic(sameCard, FormulaLogicOperator.Implies, sameBudget)));
    }

    private static Formula CardinalityPremiseNecessaryFormula()
    {
        Formula evidence = PrimeEvidenceFamily(D(0));
        return Disp(new Formula.Relation(
            Budget(evidence, Emptyset),
            FormulaRelationOperator.NotEqual,
            Budget(evidence, SingletonSet(D(2)))));
    }

    private static Formula Budget(Formula evidence, Formula indices) =>
        new Formula.Apply(F.Id("B"), [evidence, indices]);

    private static Formula Card(Formula indices) =>
        Seq(Lvert, Sp, indices, Sp, Rvert);

    private static Formula SingletonSet(Formula value) =>
        Seq(OpenBrace, value, CloseBrace);

    private static Formula ConstantFamily(Formula value) =>
        Seq(Open, F.Id("i"), Sp, Mapsto, Sp, value, Close);

    private static Formula PrimeEvidence(Formula exponent, Formula prime) =>
        new Formula.Apply(F.Id("primeEvidence"), [exponent, prime]);

    private static Formula PrimeEvidenceFamily(Formula exponent) =>
        Seq(Open, F.Id("p"), Sp, Mapsto, Sp,
            PrimeEvidence(exponent, F.Id("p")), Close);

    private static Formula NegativeOne() =>
        Seq(Minus, D(1));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
