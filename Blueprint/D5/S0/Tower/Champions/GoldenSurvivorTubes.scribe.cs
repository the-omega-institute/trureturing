using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class GoldenSurvivorTubesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var branch = Id("b");
        var f = Id("F");
        var n = Id("n");
        var state = Id("s");
        var u = Id("u");
        var v = Id("v");
        var naturals = Id("N");
        var reals = Id("R");
        var branches = Id("GoldenBackwardBranch");
        var states = Id("GoldenSurvivorState");
        var stateSets = Id("GoldenSurvivorStateSet");
        var transition = Id("goldenTransition");
        var inverse = Id("goldenInverse");
        var strictSet = Id("goldenStrictSurvivorSet");

        Formula Backward(Formula set, Formula depth) =>
            Call("goldenBackwardSurvivor", set, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var backwardStep = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("F"), stateSets),
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), naturals),
            ],
            Equal(
                Backward(f, Add(n, Num(1))),
                Call(
                    "intersection",
                    f,
                    Call("preimage", transition, Backward(f, n)))));

        var contraction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), branches),
                new Formula.BoundVariable(FormulaIdentifier.Create("u"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("v"), reals),
            ],
            Equal(
                Call(
                    "goldenFiberDistance",
                    Call("goldenBranchSourceKind", branch),
                    Call("goldenBranchCoordinate", branch, u),
                    Call("goldenBranchCoordinate", branch, v)),
                Multiply(
                    inverse,
                    Call(
                        "goldenFiberDistance",
                        Call("goldenBranchTargetKind", branch),
                        u,
                        v))));

        var depthForty = new Formula.Relation(
            new Formula.Power(inverse, Num(40)),
            FormulaRelationOperator.LessThan,
            new Formula.Fraction(Num(5), Num(1000000000)));

        var fourTubes = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), states),
            ],
            new Formula.Logic(
                Member(state, Backward(strictSet, Add(n, Num(2)))),
                FormulaLogicOperator.Iff,
                Call("goldenOpenTube", n, state)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden backward survival is an exact four-branch contracting system after two steps.",
            H("Golden Backward Survivor Tubes"),
            Blocks(
                Paragraph(Text(
                    "A state records a golden gap kind and its normalized coordinate. The "
                        + "transition follows one refinement step, and finite survival is defined "
                        + "recursively by intersecting the threshold domain with the preimage of "
                        + "the preceding survivor set.")),
                Describe.Lean(
                    DescribeId.Create("backward-survival-uses-transition-preimages"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorTubes."
                        + "golden_backward_survivor_succ"),
                    H("Backward survival uses transition preimages"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(backwardStep)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The successor is F intersected with the inverse image of the previous "
                            + "depth. This is the T inverse direction; a forward image would be a "
                            + "different recurrence and would not express continued survival."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-inverse-branches-contract-by-the-golden-inverse"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorTubes."
                        + "golden_backward_branch_contraction"),
                    H("Four inverse branches contract by the golden inverse"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(contraction)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Large and small coordinates use physical gap-length weights. In this "
                            + "metric each active affine inverse branch has contraction ratio "
                            + "exactly phi inverse, and therefore in particular at most that value."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("forty-inverse-steps-have-a-certified-radius-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorTubes."
                        + "golden_depth_forty_contraction_lt"),
                    H("Forty inverse steps have a certified radius bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(depthForty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The calculation first proves phi inverse is below 619/1000 and then "
                            + "checks the fortieth rational power. The resulting bound is 5e-9, "
                            + "which makes the source's order-of-1e-9 estimate precise."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("strict-backward-survival-is-exactly-four-open-tubes"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorTubes."
                        + "golden_backward_survivor_four_tubes"),
                    H("Strict backward survival is exactly four open tubes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fourTubes)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "After the two-level transient, exact interval algebra identifies "
                                + "every finite-depth strict survivor with one of four open tubes. "
                                + "Their lower endpoints follow the four inverse branches and their "
                                + "upper endpoints are the four claimed limiting coordinates.")),
                        Paragraph(Text(
                            "Four compile-time examples independently evaluate the transition on "
                                + "the tail point and the three cycle points. They verify the chain "
                                + "L(phi inverse over 2) to L(1/2) to L(phi/2) to S(1/2) and back "
                                + "to L(1/2)."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/GoldenGapWord")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/MetricGeometry/GoldenSurvivor")),
            ]));
    }
}
