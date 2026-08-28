using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class LocalEvidenceOrderThresholdDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear event mass and quadratic evidence have distinct prime thresholds.",
        H("Local Evidence Order Determines the Critical Exponent"),
        Blocks(
            Paragraph(Text(
                "本节不声称 α=1/2 与 Riemann 临界线具有解析等价、"
                    + "零点等价或物理因果关系。这里只存在「二次证据导致"
                    + "指数折半」的结构类比。")),
            Describe.Lean(
                DescribeId.Create("first-event-mass"),
                DeclarationHandle.Create(DeclarationPrefix + "firstEventMass"),
                H("First-event mass"),
                StatementSource.FromAuthor(FirstEventMassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named mass is the local probability formula p to the power minus s. "
                        + "A separate theorem checks its event-probability semantics."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-statistical-energy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadraticStatisticalEnergy"),
                H("Quadratic statistical energy"),
                StatementSource.FromAuthor(QuadraticEnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any index type, the energy at one coordinate is the square of its "
                        + "local deviation. No prime structure enters this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-event-mass-probability-bridge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "firstEventMass_eq_activation_probability"),
                H("First-event mass is the zeta activation probability"),
                StatementSource.FromAuthor(ActivationProbabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above exponent one, the normalized zeta law exists. Its event that the "
                        + "p-adic exponent is positive has exactly the named first-event mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-event-mass-threshold"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "firstEventMass_summable_iff_one_lt"),
                H("First-event mass has threshold one"),
                StatementSource.FromAuthor(FirstThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime-indexed activation masses are summable exactly when s is "
                        + "strictly greater than one. Prime distribution is load-bearing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-energy-doubles-order"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadratic_prime_energy_eq_firstEventMass"),
                H("Quadratic energy doubles the exponent"),
                StatementSource.FromAuthor(DoubledOrderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the deviation p to the power minus alpha, squaring changes the "
                        + "same prime family to exponent two alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-energy-threshold"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadratic_prime_energy_summable_iff_half_lt"),
                H("Quadratic energy has threshold one half"),
                StatementSource.FromAuthor(QuadraticThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The doubled exponent is above one exactly when alpha is above one half. "
                        + "The exact iff still uses the prime-series theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-evidence-order-principle"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "local_evidence_order_critical_thresholds"),
                H("Accumulated order determines the critical exponent"),
                StatementSource.FromAuthor(UnifiedPrincipleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same prime spectrum gives threshold one for linear activation mass "
                        + "and one half for quadratic evidence. The thresholds are unequal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-event-mass-below-threshold"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "firstEventMass_at_most_one_not_summable"),
                H("First-event mass diverges at and below one"),
                StatementSource.FromAuthor(AtMostOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every exponent at most one lies on the nonsummable side, including the "
                        + "boundary itself and all nonpositive exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-exponent-first-event-mass"),
                DeclarationHandle.Create(DeclarationPrefix + "firstEventMass_zero"),
                H("Zero exponent is constant and divergent"),
                StatementSource.FromAuthor(ZeroExponentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent zero every prime contributes one, so the infinite prime "
                        + "family is not summable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-deviation-energy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadraticStatisticalEnergy_zero_summable"),
                H("Zero deviation has summable energy"),
                StatementSource.FromAuthor(ZeroEnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On every index type, the zero deviation has identically zero quadratic "
                        + "energy and is summable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prime-truncation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_prime_truncation_summable"),
                H("Finite prime truncations are summable"),
                StatementSource.FromAuthor(FiniteTruncationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Restricting to finitely many primes is summable at every exponent. This "
                        + "degeneration uses finite support, not prime distribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-and-unit-energy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadratic_energy_empty_and_unit_summable"),
                H("Empty and singleton energy families are summable"),
                StatementSource.FromAuthor(EmptyUnitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every family on the empty type or the one-element unit type has finite "
                        + "support, so its quadratic energy is summable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-boundary-divergence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "quadratic_prime_energy_one_half_not_summable"),
                H("The one-half boundary diverges"),
                StatementSource.FromAuthor(HalfBoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At alpha equal to one half, quadratic energy becomes reciprocal-prime "
                        + "mass, so the boundary itself is not summable."))),
                DescribeRole.Theorem))));

    private static Formula FirstEventMassFormula()
    {
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        return Disp(new Formula.Relation(
            FirstMassAt(exponent, prime),
            FormulaRelationOperator.Equal,
            new Formula.Power(prime, Grp(Seq(Minus, exponent)))));
    }

    private static Formula QuadraticEnergyFormula()
    {
        Formula deviation = F.Id("delta");
        Formula index = F.Id("i");
        Formula localDeviation = new Formula.Subscript(deviation, index);
        return Disp(new Formula.Relation(
            EnergyAt(deviation, index),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                localDeviation,
                FormulaBinaryOperator.Multiply,
                localDeviation)));
    }

    private static Formula ActivationProbabilityFormula()
    {
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        Formula eventFormula = Seq(
            new Formula.Subscript(F.Id("V"), prime), Sp, Gt, Sp, D(0));
        Formula probability = Seq(
            new Formula.Subscript(F.Id("P"), exponent),
            Open, eventFormula, Close);
        return Disp(new Formula.Relation(
            probability,
            FormulaRelationOperator.Equal,
            FirstMassAt(exponent, prime)));
    }

    private static Formula FirstThresholdFormula()
    {
        Formula exponent = F.Id("s");
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                IsSummable(FirstMassFamily(exponent)),
                FormulaLogicOperator.Iff,
                new Formula.Relation(
                    D(1), FormulaRelationOperator.LessThan, exponent))));
    }

    private static Formula DoubledOrderFormula()
    {
        Formula exponent = F.Id("alpha");
        Formula doubled = new Formula.Binary(
            D(2), FormulaBinaryOperator.Multiply, exponent);
        return Disp(new Formula.Relation(
            EnergyFamily(FirstMassFamily(exponent)),
            FormulaRelationOperator.Equal,
            FirstMassFamily(doubled)));
    }

    private static Formula QuadraticThresholdFormula()
    {
        Formula exponent = F.Id("alpha");
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                IsSummable(EnergyFamily(FirstMassFamily(exponent))),
                FormulaLogicOperator.Iff,
                new Formula.Relation(
                    new Formula.Fraction(D(1), D(2)),
                    FormulaRelationOperator.LessThan,
                    exponent))));
    }

    private static Formula UnifiedPrincipleFormula()
    {
        Formula firstThreshold = FirstThresholdBody();
        Formula quadraticThreshold = QuadraticThresholdBody();
        Formula distinct = new Formula.Relation(
            D(1),
            FormulaRelationOperator.NotEqual,
            new Formula.Fraction(D(1), D(2)));
        return Disp(And(
            Grp(firstThreshold),
            And(Grp(quadraticThreshold), distinct)));
    }

    private static Formula AtMostOneFormula()
    {
        Formula exponent = F.Id("s");
        Formula premise = new Formula.Relation(
            exponent, FormulaRelationOperator.LessThanOrEqual, D(1));
        return Disp(Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                premise,
                FormulaLogicOperator.Implies,
                Not(IsSummable(FirstMassFamily(exponent))))));
    }

    private static Formula ZeroExponentFormula()
    {
        Formula prime = F.Id("p");
        Formula constant = Seq(
            Forall, Sp, prime, Comma, Sp,
            new Formula.Relation(
                FirstMassAt(D(0), prime),
                FormulaRelationOperator.Equal,
                D(1)));
        return Disp(And(constant, Not(IsSummable(FirstMassFamily(D(0))))));
    }

    private static Formula ZeroEnergyFormula() =>
        Disp(IsSummable(EnergyFamily(D(0))));

    private static Formula FiniteTruncationFormula()
    {
        Formula support = F.Id("S");
        Formula exponent = F.Id("s");
        Formula indicator = new Formula.Subscript(F.Id("chi"), support);
        Formula restricted = Seq(
            FirstMassFamily(exponent), Sp, indicator);
        return Disp(Seq(
            Forall, Sp, support, Comma, Sp, exponent, Comma, Sp,
            IsSummable(restricted)));
    }

    private static Formula EmptyUnitFormula()
    {
        Formula deviation = F.Id("delta");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula emptyCase = Seq(
            Forall, Sp, deviation, Colon, Sp, Emptyset, Sp, To, Sp, reals,
            Comma, Sp, IsSummable(EnergyFamily(deviation)));
        Formula unitCase = Seq(
            Forall, Sp, deviation, Colon, Sp, F.Id("Unit"), Sp, To, Sp, reals,
            Comma, Sp, IsSummable(EnergyFamily(deviation)));
        return Disp(And(Grp(emptyCase), Grp(unitCase)));
    }

    private static Formula HalfBoundaryFormula() =>
        Disp(Not(IsSummable(EnergyFamily(
            FirstMassFamily(new Formula.Fraction(D(1), D(2)))))));

    private static Formula FirstThresholdBody()
    {
        Formula exponent = F.Id("s");
        Formula threshold = new Formula.Relation(
            D(1), FormulaRelationOperator.LessThan, exponent);
        return Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                IsSummable(FirstMassFamily(exponent)),
                FormulaLogicOperator.Iff,
                threshold));
    }

    private static Formula QuadraticThresholdBody()
    {
        Formula exponent = F.Id("alpha");
        Formula threshold = new Formula.Relation(
            new Formula.Fraction(D(1), D(2)),
            FormulaRelationOperator.LessThan,
            exponent);
        return Seq(
            Forall, Sp, exponent, Comma, Sp,
            new Formula.Logic(
                IsSummable(EnergyFamily(FirstMassFamily(exponent))),
                FormulaLogicOperator.Iff,
                threshold));
    }

    private static Formula FirstMassAt(Formula exponent, Formula prime) =>
        Seq(FirstMassFamily(exponent), Open, prime, Close);

    private static Formula FirstMassFamily(Formula exponent) =>
        Seq(F.Id("m"), Open, exponent, Close);

    private static Formula EnergyAt(Formula deviation, Formula index) =>
        Seq(EnergyFamily(deviation), Open, index, Close);

    private static Formula EnergyFamily(Formula deviation) =>
        Seq(F.Id("E"), Open, deviation, Close);

    private static Formula IsSummable(Formula family) =>
        new Formula.Apply(F.Id("Summable"), [family]);

    private static Formula Not(Formula formula) =>
        Seq(Neg, Sp, formula);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
