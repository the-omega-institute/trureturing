using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.ErgodicBridge;

internal sealed class GeneralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var bridge = Id("bridge");
        var naturals = Id("N");
        var bridges = Id("DBonacciErgodicBridge");

        var orderBound = new Formula.Relation(
            d,
            FormulaRelationOperator.GreaterThanOrEqual,
            Num(2));
        var valueSetsEqual = Equal(
            Call("gridLowerValues", bridge),
            Call("ergodicLowerValues", bridge));
        var optimalValuesEqual = Equal(
            Call("gridOptimalValue", bridge),
            Call("ergodicOptimalValue", bridge));

        Formula ForEveryBridge(Formula conclusion) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("bridge"), bridges),
            ],
            new Formula.Logic(
                orderBound,
                FormulaLogicOperator.Implies,
                conclusion));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A Fin-d typed coding identifies d-bonacci grid and ergodic lower-value optima.",
            H("General D-Bonacci Ergodic Bridge"),
            Blocks(
                Paragraph(Text(
                    "The changing gap spectrum is represented by the existing Fin d alphabet. "
                        + "Each instance supplies its gap extents, coding transition, and one "
                        + "grid realization uniformly for every letter.")),
                Paragraph(Text(
                    "The general proof then iterates the coding, removes the finite prefix in "
                        + "the liminf, proves both realization directions, and compares the two "
                        + "attained-value sets.")),
                Describe.Lean(
                    DescribeId.Create("general-grid-and-orbit-lower-value-sets-are-equal"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/General.lower_value_sets_eq"),
                    H("General grid and orbit lower-value sets are equal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(ForEveryBridge(valueSetsEqual))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Forward coding maps every admissible grid value to a unit orbit. The "
                            + "Fin d realization family maps every unit orbit value back to the "
                            + "fixed realization level."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-d-bonacci-objective-is-ergodic-optimization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/ErgodicBridge/General."
                            + "optimal_value_eq_ergodic_optimal_value"),
                    H("The general d-bonacci objective is ergodic optimization"),
                    StatementSource.FromAuthor(
                        FormulaDsl.Disp(ForEveryBridge(optimalValuesEqual))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Taking suprema of the equal attained-value sets identifies the grid "
                            + "champion objective with maximin optimization of the state arm."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/GapAlphabet")),
            ]));
    }
}
