using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.ErgodicBridge;

internal sealed class TribonacciDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q0");
        var x = Id("x");
        var state = Id("state");
        var naturals = Id("N");
        var reals = Id("R");
        var states = Id("TribonacciPeriodicState");
        var gridValues = Id("tribonacciGridLowerValues");
        var orbitValues = Id("tribonacciErgodicLowerValues");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var hullMembership = Member(x, Call("tribonacciNameHull", q));
        var lowerValueEquality = Equal(
            Call("liminf", Call("tribonacciSurvivorLevels", x)),
            Call("tribonacciOrbitLowerValue", state));
        var forwardConclusion = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("state"),
            states,
            new Formula.Logic(
                Call("TribonacciUnitState", state),
                FormulaLogicOperator.And,
                lowerValueEquality));
        var forwardBridge = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Q0"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
            ],
            new Formula.Logic(
                hullMembership,
                FormulaLogicOperator.Implies,
                forwardConclusion));

        var reverseConclusion = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Logic(
                Member(x, Call("tribonacciNameHull", Num(3))),
                FormulaLogicOperator.And,
                lowerValueEquality));
        var reverseBridge = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("state"),
            states,
            new Formula.Logic(
                Call("TribonacciUnitState", state),
                FormulaLogicOperator.Implies,
                reverseConclusion));
        var valueSetsEqual = Equal(gridValues, orbitValues);
        var optimalValuesEqual = Equal(
            Id("tribonacciGridOptimalValue"),
            Id("tribonacciErgodicOptimalValue"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Tribonacci name-grid liminf is exactly the lower arm value of a three-gap orbit.",
            H("Tribonacci Ergodic Bridge"),
            Blocks(
                Paragraph(Text(
                    "The observable is the nearer normalized arm in the current small, combined, "
                        + "or large gap. It is compared by liminf, not by a Birkhoff average.")),
                Paragraph(Text(
                    "The carrier is the internal name-grid hull. The omitted right terminal point "
                        + "has a one-sided terminal gap and is not a state of the two-ended map.")),
                Describe.Lean(
                    DescribeId.Create(
                        "every-internal-grid-point-has-an-equal-three-gap-orbit-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge"),
                    H("Every internal grid point has an equal three-gap orbit value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(forwardBridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every internal grid point determines its containing gap letter and arm "
                            + "coordinate. The five refinement branches preserve this coding, so "
                            + "discarding the finite initial prefix identifies the liminf "
                            + "values."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("every-typed-unit-state-has-an-internal-grid-realization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_ergodic_bridge_reverse"),
                    H("Every typed unit state has an internal grid realization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(reverseBridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Certified small, combined, and large gaps at level three realize every "
                            + "coordinate in their typed state intervals. The dynamical state "
                            + "space therefore contributes no additional lower values."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-grid-and-orbit-lower-value-sets-are-equal"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Tribonacci.tribonacci_lower_value_sets_eq"),
                    H("Tribonacci grid and orbit lower-value sets are equal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valueSetsEqual)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The forward and three-type reverse realizations identify the full sets "
                            + "of attained lower asymptotic values, not only a periodic "
                            + "champion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-champion-objective-is-ergodic-optimization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Tribonacci."
                            + "tribonacci_optimal_value_eq_ergodic_optimal_value"),
                    H("The Tribonacci champion objective is ergodic optimization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(optimalValuesEqual)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Taking the supremum of the equal value sets turns the internal name-grid "
                            + "champion objective into optimization of the lower arm observable "
                            + "on the piecewise linear three-gap map."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/ChampionOrbit")),
            ]));
    }
}
