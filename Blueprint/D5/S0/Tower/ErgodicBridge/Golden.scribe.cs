using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.ErgodicBridge;

internal sealed class GoldenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q0");
        var x = Id("x");
        var state = Id("state");
        var naturals = Id("N");
        var reals = Id("R");
        var states = Id("GoldenSurvivorState");
        var gridValues = Id("goldenGridLowerValues");
        var orbitValues = Id("goldenErgodicLowerValues");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var levelBound = new Formula.Relation(
            q,
            FormulaRelationOperator.GreaterThanOrEqual,
            Num(2));
        var hullMembership = Member(x, Call("goldenNameHull", q));
        var forwardPremise = new Formula.Logic(
            levelBound,
            FormulaLogicOperator.And,
            hullMembership);
        var lowerValueEquality = Equal(
            Call("liminf", Call("goldenSurvivorLevels", x)),
            Call("goldenOrbitLowerValue", state));
        var forwardConclusion = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("state"),
            states,
            new Formula.Logic(
                Call("GoldenUnitState", state),
                FormulaLogicOperator.And,
                lowerValueEquality));
        var forwardBridge = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Q0"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
            ],
            new Formula.Logic(
                forwardPremise,
                FormulaLogicOperator.Implies,
                forwardConclusion));

        var reverseConclusion = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Logic(
                Member(x, Call("goldenNameHull", Num(2))),
                FormulaLogicOperator.And,
                lowerValueEquality));
        var reverseBridge = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("state"),
            states,
            new Formula.Logic(
                Call("GoldenUnitState", state),
                FormulaLogicOperator.Implies,
                reverseConclusion));
        var valueSetsEqual = Equal(gridValues, orbitValues);
        var optimalValuesEqual = Equal(
            Id("goldenGridOptimalValue"),
            Id("goldenErgodicOptimalValue"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden name-grid liminf is exactly the lower arm value of an expanding gap orbit.",
            H("Golden Ergodic Bridge"),
            Blocks(
                Paragraph(Text(
                    "The observable is the nearer normalized gap arm. It is compared by liminf, "
                        + "not by a Birkhoff average: at every refinement level it equals the "
                        + "name-grid survivor, and on a periodic orbit its liminf is the orbit minimum.")),
                Paragraph(Text(
                    "The carrier is the internal name-grid hull. The omitted right terminal point "
                        + "has a one-sided terminal gap and is not a state of this two-ended "
                        + "expanding map.")),
                Describe.Lean(
                    DescribeId.Create("every-internal-grid-point-has-an-equal-orbit-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge"),
                    H("Every internal grid point has an equal orbit value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(forwardBridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every starting level at least two and every point in its internal "
                            + "name-grid hull, a unit gap state codes the point. Gap substitution "
                            + "preserves that coding, so the two liminf values are equal after "
                            + "discarding the finite initial prefix."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("every-unit-state-has-an-internal-grid-realization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Golden.golden_ergodic_bridge_reverse"),
                    H("Every unit state has an internal grid realization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(reverseBridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A certified large gap and small gap at level two realize every coordinate "
                            + "in the unit interval. Thus the dynamical state space introduces no "
                            + "extra lower values absent from the internal name-grid problem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("grid-and-orbit-lower-value-sets-are-equal"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Golden.golden_lower_value_sets_eq"),
                    H("Grid and orbit lower-value sets are equal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valueSetsEqual)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The forward and reverse realizations identify the full sets of attained "
                            + "lower asymptotic values, rather than only the known champion point."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-champion-objective-is-ergodic-optimization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/Golden."
                            + "golden_optimal_value_eq_ergodic_optimal_value"),
                    H("The golden champion objective is ergodic optimization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(optimalValuesEqual)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Taking the supremum of the equal value sets turns the internal name-grid "
                            + "champion objective into maximin optimization of the lower arm "
                            + "observable on the piecewise linear expanding map."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenAsymptotic")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenSurvivorTubes")),
            ]));
    }
}
