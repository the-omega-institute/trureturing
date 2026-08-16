using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class GoldenSurvivorClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var state = Id("s");
        var x = Id("x");
        var naturals = Id("N");
        var reals = Id("R");
        var states = Id("GoldenSurvivorState");
        var inverse = Id("goldenInverse");
        var threshold = Id("goldenThreshold");
        var closedSet = Id("goldenClosedSurvivorSet");
        var strictSet = Id("goldenStrictSurvivorSet");
        var fourPointSet = Id("goldenFourPointSet");

        Formula Backward(Formula set, Formula depth) =>
            Call("goldenBackwardSurvivor", set, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula Permanent(Formula value, Formula set) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Member(value, Backward(set, n)));

        Formula GoldenLiminf(Formula value) =>
            Call("liminf", Call("goldenSurvivorSequence", value), Id("atTop"));

        var limitCore = Equal(Id("goldenBackwardLimitCore"), fourPointSet);

        var noStrictPermanent = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("s"),
            states,
            new Formula.Not(Permanent(state, strictSet)));

        var closedCounterexample = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"),
            states,
            new Formula.Logic(
                Permanent(state, closedSet),
                FormulaLogicOperator.And,
                new Formula.Not(Member(state, fourPointSet))));

        var endpointLiminf = Equal(GoldenLiminf(Num(1)), inverse);

        var unrestrictedBoundFalse = new Formula.Not(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Relation(
                GoldenLiminf(x),
                FormulaRelationOperator.LessThanOrEqual,
                threshold)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The four strict survivor tubes have the claimed limit, while two stronger source conclusions are false.",
            H("Golden Survivor Classification"),
            Blocks(
                Paragraph(Text(
                    "The exact finite-depth tubes shrink componentwise to the tail state and the "
                        + "three-state champion cycle. Closing each fixed tube before intersecting "
                        + "over all depths preserves exactly those four component endpoints.")),
                Describe.Lean(
                    DescribeId.Create("componentwise-closed-tube-limit-is-four-points"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorClassification."
                        + "golden_backward_limit_core_eq_four_points"),
                    H("The componentwise closed tube limit is four points"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(limitCore)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The four tube radii are bounded by powers of phi inverse. Any point on "
                            + "the same side of a limiting endpoint is excluded at a sufficiently "
                            + "deep level, while each endpoint belongs to every componentwise "
                            + "closed tube."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("no-state-survives-the-strict-threshold-forever"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorClassification."
                        + "golden_no_strict_permanent_survivor"),
                    H("No state survives the strict threshold forever"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(noStrictPermanent)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Permanent strict survival would put a state in every componentwise "
                            + "closed tube and hence among the four endpoints. The depth-two open "
                            + "tube formula excludes each of those endpoints, giving the required "
                            + "classification-to-survival argument rather than an unsupported jump."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("closed-permanent-survival-is-not-four-points"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorClassification."
                        + "golden_closed_permanent_not_four_points"),
                    H("Closed permanent survival is not four points"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(closedCounterexample)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Closing the threshold set before backward iteration is different from "
                            + "closing each of the four nondegenerate strict components. An explicit "
                            + "higher preimage remains in the closed threshold set along its entire "
                            + "preperiodic orbit but is not one of the four listed states. Thus the "
                            + "source's closed-permanent four-point claim is false."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("terminal-point-liminf-is-the-golden-inverse"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorClassification."
                        + "golden_survivor_one_liminf"),
                    H("The terminal point liminf is the golden inverse"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(endpointLiminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For the frozen real-line survivor, x equal to one is outside the indexed "
                            + "name grid but its distance to the grid is the completed terminal gap. "
                            + "Exact Zeckendorf endpoint calculations give survivor values one at "
                            + "even levels and phi inverse at odd levels, so the liminf is phi inverse."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("unrestricted-global-liminf-bound-is-false"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenSurvivorClassification."
                        + "golden_global_liminf_upper_bound_false"),
                    H("The unrestricted global liminf bound is false"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(unrestrictedBoundFalse)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The terminal-point liminf phi inverse is strictly larger than phi "
                            + "inverse squared over two. Therefore the requested statement for all "
                            + "real x, and consequently its stated real-line supremum equality, "
                            + "cannot be proved from the frozen definition because it is false."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenSurvivorTubes")),
            ]));
    }
}
