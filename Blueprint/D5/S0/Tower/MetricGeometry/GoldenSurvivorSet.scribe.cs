using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.MetricGeometry;

internal sealed class GoldenSurvivorSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var x = Id("x");
        var i = Id("i");
        var naturals = Id("N");
        var reals = Id("R");
        var half = new Formula.Fraction(Num(1), Num(2));
        var hull = Call("goldenNameHull", q);
        var survivor = Call("goldenSurvivor", q, x);
        var maximizers = Call("goldenSurvivorMaximizers", q);
        var largeIndices = Call("goldenLargeGapIndices", q);

        Formula ForAllQ(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden-survivor maximizers are exactly the midpoints of the largest internal gaps.",
            H("Golden Survivor Maximizer Set"),
            Blocks(
                Paragraph(Text(
                    "Restricting normalized distance to the golden-name hull turns the maximum "
                        + "value into a finite classification problem. The ordered grid has no "
                        + "hidden maximizers: equality forces both endpoint bounds to be sharp.")),
                Describe.Lean(
                    DescribeId.Create("golden-survivor-half-iff-largest-gap-midpoint"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivorSet."
                        + "goldenSurvivor_eq_half_iff"),
                    H("One half is attained exactly at largest-gap midpoints"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        new Formula.Logic(
                            Call("memberOf", x, hull),
                            FormulaLogicOperator.Implies,
                            new Formula.Logic(
                                Equal(survivor, half),
                                FormulaLogicOperator.Iff,
                                new Formula.Bind(
                                    FormulaQuantifier.Exists,
                                    FormulaIdentifier.Create("i"),
                                    Call("internalGapIndex", q),
                                    new Formula.Logic(
                                        Call("isGoldenLargeGap", q, i),
                                        FormulaLogicOperator.And,
                                        Equal(x, Call("goldenGapMidpoint", q, i))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a point in one adjacent cell, distance to each endpoint bounds "
                            + "infimum distance. Equality at one half makes both inequalities "
                            + "equalities, so the cell is large and the point is its midpoint. "
                            + "Conversely, strict grid order puts every grid point outside a large "
                            + "gap, making its midpoint exactly half a large gap from the grid."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("maximizers-and-large-gaps-have-equal-cardinality"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivorSet."
                        + "golden_survivor_maximizer_ncard"),
                    H("Maximizers and largest internal gaps have equal cardinality"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(1)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call("ncard", maximizers),
                            Call("card", largeIndices))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Gap midpoints are strictly increasing, hence injective. The iff theorem "
                            + "identifies the maximizer set with the image of the filtered internal "
                            + "gap indices, so finite image cardinality is preserved exactly."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("internal-large-gap-count-from-full-frequency"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivorSet."
                        + "golden_internal_large_gap_count"),
                    H("The full frequency counts internal gaps plus the terminal correction"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(2)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Add(
                                Call("card", largeIndices),
                                Call("terminalLargeIndicator", q)),
                            Call("Fib", Add(q, Num(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The internal gap embedding identifies its filtered image with the full "
                            + "large-gap filter after deleting the terminal boundary gap. The frozen "
                            + "full-gap frequency then supplies Fib(Q+1), with a one-or-zero terminal "
                            + "correction read from the frozen gap word."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("level-four-survivor-has-four-maximizers"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivorSet."
                        + "golden_survivor_four_point_ncard"),
                    H("The level-four survivor has four maximizers"),
                    StatementSource.FromAuthor(Equal(
                        Call("ncard", Call("goldenSurvivorMaximizers", Num(4))),
                        Num(4))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At level four the Fibonacci gap word ends in a large letter. Removing "
                            + "that terminal gap from the five full large gaps leaves four internal "
                            + "large gaps, and therefore exactly four maximizing hull points."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("champion-level-survivor-has-twelve-maximizers"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivorSet."
                        + "golden_survivor_champion_level_ncard"),
                    H("The champion level has twelve metric maximizers"),
                    StatementSource.FromAuthor(Equal(
                        Call("ncard", Call("goldenSurvivorMaximizers", Num(6))),
                        Num(12))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The closed-form champion point belongs to level six. At that level the "
                            + "full frequency has thirteen large gaps and the gap word again ends "
                            + "in a large letter, leaving twelve internal maximizing midpoints. "
                            + "Thus this metric maximizer set is not the source's separate four-state "
                            + "dynamical survivor orbit."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/MetricGeometry/GoldenSurvivor")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGapWord")),
            ]));
    }
}
