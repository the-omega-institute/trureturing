using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.MetricGeometry;

internal sealed class GoldenSurvivorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var x = Id("x");
        var phi = Id("phi");
        var naturals = Id("N");
        var reals = Id("R");
        var half = new Formula.Fraction(Num(1), Num(2));
        var survivor = Call("goldenSurvivor", q, x);
        var hull = Call("goldenNameHull", q);
        var eventualBounds = Call("goldenSurvivorBounds", q);

        Formula ForAllQ(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden-name grid distance has an exact global normalized supremum on its hull.",
            H("Golden Survivor Extremality"),
            Blocks(
                Paragraph(Text(
                    "The level-Q golden-name grid is the finite image of indexedNameValue. "
                        + "Because this image is finite, distance to it is unbounded on the whole "
                        + "real line. The natural global domain is therefore its hull, tiled by "
                        + "the closed intervals between consecutive indexed values.")),
                Describe.Lean(
                    DescribeId.Create("golden-name-grid-is-the-name-value-image"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor."
                        + "goldenNameGrid_eq_nameValue_range"),
                    H("The golden grid is the intrinsic name-value image"),
                    StatementSource.FromAuthor(ForAllQ(Equal(
                        Call("goldenNameGrid", q),
                        Call("range", Call("nameValue", q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen equivalence between the Fibonacci interval and GoldenName "
                            + "is surjective in both directions, so the indexed and intrinsic "
                            + "descriptions determine exactly the same real grid."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("normalized-golden-survivor-carrier"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor.goldenSurvivor"),
                    H("Normalized golden survivor carrier"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        Equal(
                            survivor,
                            Multiply(
                                new Formula.Power(phi, q),
                                Call(
                                    "infDist",
                                    x,
                                    Call("goldenNameGrid", q))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The carrier multiplies metric infimum distance to the actual finite "
                            + "golden-name grid by phi to the level. This is the direct golden "
                            + "analogue of normalized radixDistance."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("golden-survivor-is-globally-at-most-one-half"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor."
                        + "goldenSurvivor_le_half"),
                    H("Every hull point has survivor value at most one half"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        new Formula.Logic(
                            Call("memberOf", x, hull),
                            FormulaLogicOperator.Implies,
                            new Formula.Relation(
                                survivor,
                                FormulaRelationOperator.LessThanOrEqual,
                                half))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each hull point lies in an adjacent golden cell. Distance to one of "
                            + "the two endpoints is at most half that cell length, and the frozen "
                            + "two-gap theorem bounds every cell by phi to the minus Q. "
                            + "Normalization therefore gives the global one-half ceiling."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("first-golden-midpoint-realizes-the-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor."
                        + "first_golden_midpoint_realizes"),
                    H("The first large-gap midpoint realizes one half"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(1)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call(
                                "goldenSurvivor",
                                q,
                                Call("firstGoldenMidpoint", q)),
                            half)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The first adjacent gap has exact length phi to the minus Q. Strict "
                            + "monotonicity places every other grid point outside that gap, so "
                            + "its midpoint is exactly half a large gap from the entire grid."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("global-golden-survivor-supremum-is-one-half"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor."
                        + "golden_survivor_global_sup"),
                    H("The global golden survivor supremum is one half"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(1)),
                        FormulaLogicOperator.Implies,
                        Equal(Call("sSup", eventualBounds), half)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The pointwise theorem bounds every attainable lower value by one half. "
                            + "The first large-gap midpoint belongs to the hull and attains one "
                            + "half, so the supremum of all realized lower values is exactly one "
                            + "half at every positive level."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("closed-form-golden-champion-realizes-the-maximum"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/GoldenSurvivor."
                        + "golden_champion_point_realizes"),
                    H("The closed-form golden champion realizes the level-six maximum"),
                    StatementSource.FromAuthor(Equal(
                        Call(
                            "goldenSurvivor",
                            Num(6),
                            Subtract(
                                new Formula.Fraction(Num(13), Num(2)),
                                Multiply(Num(4), phi))),
                        half)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen champion identity identifies thirteen halves minus four phi "
                            + "with phi to the minus six divided by two. That is the first "
                            + "level-six large-gap midpoint, so it realizes the global maximum."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGaps")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenChampionPoint")),
            ]));
    }
}
