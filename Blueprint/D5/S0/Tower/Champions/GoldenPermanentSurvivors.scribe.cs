using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class GoldenPermanentSurvivorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("GoldenSurvivorState");
        var strictSet = Id("goldenStrictSurvivorSet");
        var closedSet = Id("goldenClosedSurvivorSet");

        Formula Backward(Formula set, Formula depth) =>
            Call("goldenBackwardSurvivor", set, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula Permanent(Formula value, Formula set) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Member(value, Backward(set, n)));

        var strictPermanentSetEmpty = Equal(
            Id("goldenStrictPermanentSet"),
            Id("emptySet"));

        var knownClosedCarrier = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("s"),
            states,
            new Formula.Logic(
                Call("IsGoldenKnownClosedPreperiodicState", state),
                FormulaLogicOperator.Implies,
                Permanent(state, closedSet)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Strict golden survival has no permanent state; the closed threshold has a larger "
                + "proved preperiodic carrier.",
            H("Golden Permanent Survivors"),
            Blocks(
                Paragraph(Text(
                    "The source conflated two different constructions. Intersecting the closures "
                        + "of the four strict finite-depth tubes gives four limiting points, but "
                        + "permanent survival for the closed threshold also retains boundary "
                        + "preimages. The strict threshold is the usable replacement for the "
                        + "upper-bound argument.")),
                Describe.Lean(
                    DescribeId.Create("strict-permanent-survivor-set-is-empty"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPermanentSurvivors."
                        + "golden_strict_permanent_set_eq_empty"),
                    H("The strict permanent survivor set is empty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(strictPermanentSetEmpty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The pointwise classification places any hypothetical strict permanent "
                            + "state in the four-point closed-tube limit. Each of those four "
                            + "points is an excluded endpoint of the open depth-two tubes, so no "
                            + "state survives every strict backward depth."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("known-closed-preperiodic-carrier-survives"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenPermanentSurvivors."
                        + "golden_known_closed_preperiodic_carrier_subset"),
                    H("The known closed preperiodic carrier survives"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(knownClosedCarrier)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proved carrier has eight states: the large-gap threshold point plus "
                            + "the frozen seven-state carrier. The threshold point maps directly "
                            + "to the tail. The counterexample used by the frozen theorem is the "
                            + "large-gap state with coordinate (9 minus 5 phi) over 2; its orbit "
                            + "passes through the large coordinate (4 phi minus 5) over 2, the "
                            + "small and large tail coordinates phi inverse over 2, and then the "
                            + "three-state champion cycle. The inclusion is deliberately not "
                            + "stated as equality and does not claim a complete closed-set "
                            + "classification."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/Champions/GoldenSurvivorClassification")),
            ]));
    }
}
