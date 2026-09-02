using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class TrajectoryCodeLedgerCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal normalized trajectories have unique coordinates and code-ledger identity.",
        H("Trajectory Code-Ledger Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("legal-trajectory-code-ledger-covariance"),
                DeclarationHandle.Create(
                    "D5/S1/Dynamics/TrajectoryCodeLedgerCovariance."
                    + "legal_trajectory_code_ledger_covariance"),
                H("Legal trajectories have unique codes and binary identity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A legal event and every state coordinate use the existing finitely "
                        + "supported canonical prime-axis table. The trajectory advances by the "
                        + "existing rowwise normalizer. The theorem states both that its actual "
                        + "next coordinate satisfies the canonical axiswise sum and decoder law, "
                        + "and that any two coordinates satisfying those laws are equal. Thus "
                        + "stepwise uniqueness is not encoded by defining a witness to be the "
                        + "desired result.")),
                    Paragraph(Text(
                        "The ledger carrier is a rule coordinate paired with the remaining ledger "
                        + "state. Adjacent preservation is iterated to prove that the rule is "
                        + "constant across the orbit. Applying the frozen code-ledger identity "
                        + "theorem then removes that fixed coordinate and yields the binary "
                        + "criterion. The two stated consequences, code change forcing state "
                        + "change and state equality forcing code equality, are exposed separately.")),
                    Paragraph(Text(
                        "Pinned library searches found generic unique-existence, equivalence "
                        + "injectivity, and product extensionality, but no trajectory theorem on "
                        + "the repository's prime-axis and ledger carriers. The proof instead "
                        + "composes the frozen unique-normalization and code-ledger declarations; "
                        + "it introduces no new carrier or normalization definition."))),
                DescribeRole.Theorem))));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula ForAll(
        IReadOnlyList<Formula.BoundVariable> binders,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);

    private static Formula TheoremFormula()
    {
        Formula rules = Id("Rules");
        Formula ledgerType = Id("Ledger");
        Formula t = Id("t");
        Formula i = Id("i");
        Formula j = Id("j");
        Formula p = Id("p");
        Formula left = Id("left");
        Formula right = Id("right");
        Formula type = Call("Type");
        Formula nat = Call("Nat");
        Formula table = Call("PrimeAxisTable");
        Formula primeAxis = Call("PrimeAxis");
        Formula stateType = Call("CodeLedgerState", Call("Prod", rules, ledgerType));

        Formula Successor(Formula n) => Add(n, Num(1));
        Formula StateAt(Formula n) => Call("trajectory", n);
        Formula EventAt(Formula n) => Call("events", n);
        Formula CoordinateAt(Formula n) => Call("coordinate", StateAt(n));
        Formula RuleAt(Formula n) => Call("rule", Call("ledger", StateAt(n)));
        Formula LedgerAt(Formula n) => Call("stateLedger", Call("ledger", StateAt(n)));
        Formula CodeAt(Formula n) => Call("canonicalCode", StateAt(n));
        Formula DigitsAt(Formula value, Formula axis) => Call("digits", value, axis);

        Formula AxisLaw(Formula value, Formula time) =>
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("p"),
                primeAxis,
                And(
                    Call("CanonicalRaw", DigitsAt(value, p)),
                    Equal(
                        Call("rawValue", DigitsAt(value, p)),
                        Add(
                            Call("rawValue", DigitsAt(CoordinateAt(time), p)),
                            Call("rawValue", DigitsAt(EventAt(time), p))))));

        Formula StepSpecification(Formula value, Formula time) =>
            And(
                AxisLaw(value, time),
                Equal(
                    Call("decodePrimeAxisTable", value),
                    Multiply(
                        Call("decodePrimeAxisTable", CoordinateAt(time)),
                        Call("decodePrimeAxisTable", EventAt(time)))));

        Formula coordinateStepType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            nat,
            Equal(
                CoordinateAt(Successor(t)),
                Call("normalizedPrimeAxisAdd", CoordinateAt(t), EventAt(t))));
        Formula ruleStepType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            nat,
            Equal(RuleAt(Successor(t)), RuleAt(t)));

        Formula stepwiseExistence = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            nat,
            StepSpecification(CoordinateAt(Successor(t)), t));
        Formula stepwiseUniqueness = ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("t"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("left"), table),
                new Formula.BoundVariable(FormulaIdentifier.Create("right"), table),
            ],
            Implies(
                StepSpecification(left, t),
                Implies(StepSpecification(right, t), Equal(left, right))));
        Formula ruleConstancy = ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("i"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), nat),
            ],
            Equal(RuleAt(i), RuleAt(j)));
        Formula identityCriterion = ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("i"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), nat),
            ],
            new Formula.Logic(
                Equal(StateAt(i), StateAt(j)),
                FormulaLogicOperator.Iff,
                And(Equal(CodeAt(i), CodeAt(j)), Equal(LedgerAt(i), LedgerAt(j)))));
        Formula codeChange = ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("i"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), nat),
            ],
            Implies(NotEqual(CodeAt(i), CodeAt(j)), NotEqual(StateAt(i), StateAt(j))));
        Formula unchangedCode = ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("i"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), nat),
            ],
            Implies(Equal(StateAt(i), StateAt(j)), Equal(CodeAt(i), CodeAt(j))));
        Formula clauses = And(
            stepwiseExistence,
            And(
                stepwiseUniqueness,
                And(
                    ruleConstancy,
                    And(identityCriterion, And(codeChange, unchangedCode)))));

        return FormulaDsl.Disp(ForAll(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Rules"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("Ledger"), type),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("events"),
                    new Formula.TypeArrow(nat, table)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("trajectory"),
                    new Formula.TypeArrow(nat, stateType)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("coordinateStep"),
                    coordinateStepType),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("ruleStep"),
                    ruleStepType),
            ],
            clauses));
    }
}
