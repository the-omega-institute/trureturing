using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class LocalDescentGlobalCompatibilityDocument : IScribeDocumentDefinition
{
    private const string DeclarationRoot =
        "D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite local descent requires separate transition, inverse-limit image, and cocycle "
            + "checks before it becomes a compatible global descent.",
        H("Local Descent and Global Gluing Compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truncated-natural-refinement-system"),
                DeclarationHandle.Create(DeclarationRoot + "truncatedNaturalSystem"),
                H("Natural numbers form a tower of finite truncations"),
                StatementSource.FromAuthor(TruncatedSystemFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At level n the coordinate carrier is Fin(n+1). A natural number is read as "
                        + "its minimum with n, and restriction to the preceding level truncates "
                        + "once more. The minimum identities supply the transition laws."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-compatible-thread"),
                DeclarationHandle.Create(DeclarationRoot + "escapingThread"),
                H("The maximal finite coordinates form a compatible thread"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Call("escapingThread", F.Id("n")), Sp, Eq, Sp, F.Id("n"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The thread selects the largest element n at level n. Restriction sends the "
                        + "largest element at level n+1 to the largest element at level n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("every-finite-readout-is-surjective"),
                DeclarationHandle.Create(
                    DeclarationRoot + "every_finite_readout_is_surjective"),
                H("Every finite truncation is realized"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Call("Surjective", Call("readout", F.Id("truncatedNaturalSystem"),
                        F.Id("n"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coordinate y in Fin(n+1) is realized by the natural number y itself, "
                        + "because truncating y at n leaves it unchanged."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("escaping-thread-is-outside-the-global-image"),
                DeclarationHandle.Create(
                    DeclarationRoot + "escaping_thread_not_in_global_image"),
                H("The compatible maximal thread has no global realization"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("escapingThread"), Sp, Neg, InMacro, Sp,
                    Call("range", Call("stateThread", F.Id("truncatedNaturalSystem"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a natural number x realized the thread, its coordinate at level x+1 "
                        + "would have to equal both x and x+1. Thus levelwise realizability does "
                        + "not imply membership in the global state-thread image."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("local-descent-requires-global-gluing-checks"),
                DeclarationHandle.Create(
                    DeclarationRoot + "local_descent_requires_global_gluing_checks"),
                H("Local closure leaves three global gluing obligations"),
                StatementSource.FromAuthor(GlobalChecksFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first public clause reuses the frozen two-chart witness: each chart "
                            + "is normalized and additive, but disagreement on their shared event "
                            + "precludes a global restriction. This is an explicit local-to-global "
                            + "countermodel, not a converse hidden in a premise.")),
                    Paragraph(Text(
                        "The second clause exposes the independent inverse-limit image check via "
                            + "the finite truncation tower. The third reuses the frozen criterion "
                            + "that transition-compatible global coefficients exist exactly when "
                            + "the unit-valued transition cocycle is a coboundary."))),
                DescribeRole.Theorem))));

    private static Formula TruncatedSystemFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), Comma, Sp,
        Call("Coordinate", F.Id("truncatedNaturalSystem"), F.Id("n")), Sp, Eq, Sp,
        Call("Fin", Seq(F.Id("n"), Plus, D(1))), Comma, Sp,
        Forall, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Call("readout", F.Id("truncatedNaturalSystem"), F.Id("n"), F.Id("x")),
        Sp, Eq, Sp, Call("min", F.Id("x"), F.Id("n")), Comma, Sp,
        Forall, Sp, F.Id("y"), InMacro, Sp, Call("Fin", Seq(F.Id("n"), Plus, D(2))),
        Comma, Sp,
        Call("restrict", F.Id("truncatedNaturalSystem"), F.Id("n"), F.Id("y")),
        Sp, Eq, Sp, Call("min", F.Id("y"), F.Id("n")), Dot));

    private static Formula LocalCountermodelFormula()
    {
        Formula context = F.Id("c");
        Formula globalValue = F.Id("globalValue");
        Formula support = F.Id("witnessEventSupport");
        Formula local = F.Id("incompatibleWitnessLocalValue");

        return Seq(
            OpenBracket,
            Forall, Sp, context, Comma, Sp,
            Call("incompatibleWitnessLocalValue", context,
                Call("witnessAtomSupport", context)), Sp, Eq, Sp, D(1),
            Sp, Land, Sp,
            Call("IsContextwiseAdditive", support, F.Id("IsDisjointUnion"), local),
            Sp, Land, Sp, Neg, Sp,
            Exists, Sp, globalValue, Colon, Sp,
            Call("CoveredEvent", support), Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Call("RestrictsToContexts", support, local, globalValue),
            CloseBracket);
    }

    private static Formula InverseImageFormula() => Seq(
        OpenBracket,
        Forall, Sp, F.Id("n"), Comma, Sp,
        Call("Surjective", Call("readout", F.Id("truncatedNaturalSystem"), F.Id("n"))),
        Sp, Land, Sp,
        F.Id("escapingThread"), Sp, Neg, InMacro, Sp,
        Call("range", Call("stateThread", F.Id("truncatedNaturalSystem"))),
        CloseBracket);

    private static Formula TransitionCriterionFormula()
    {
        Formula index = F.Id("Index");
        Formula baseType = F.Id("Base");
        Formula units = F.Id("UnitGroup");
        Formula overlap = F.Id("overlap");
        Formula transition = F.Id("transition");
        Formula global = F.Id("globalFrameCoefficients");
        Formula localUnit = F.Id("localUnit");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");

        Formula globalCompatibility = Seq(
            Exists, Sp, global, Colon, Sp, index, Sp, To, Sp, baseType, Sp, To, Sp,
            units, Comma, Sp,
            Forall, Sp, i, Comma, Sp, j, Comma, Sp, x, Comma, Sp,
            Call("overlap", i, j, x), Sp, Rightarrow, Sp,
            Call("globalFrameCoefficients", i, x), Sp, Eq, Sp,
            Call("transition", i, j, x), Sp, Cdot, Sp,
            Call("globalFrameCoefficients", j, x));

        Formula coboundary = Seq(
            Exists, Sp, localUnit, Colon, Sp, index, Sp, To, Sp, baseType, Sp, To, Sp,
            units, Comma, Sp,
            Forall, Sp, i, Comma, Sp, j, Comma, Sp, x, Comma, Sp,
            Call("overlap", i, j, x), Sp, Rightarrow, Sp,
            Call("transition", i, j, x), Sp, Eq, Sp,
            Call("inverse", Call("localUnit", i, x)), Sp, Cdot, Sp,
            Call("localUnit", j, x));

        return Seq(
            OpenBracket,
            Forall, Sp, index, Comma, Sp, baseType, Comma, Sp, units, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Group", units), CloseBracket, Comma, Sp,
            overlap, Colon, Sp, index, Sp, To, Sp, index, Sp, To, Sp,
            baseType, Sp, To, Sp,
            Operatorname, Grp(F.Id("Prop")), Comma, Sp,
            transition, Colon, Sp, index, Sp, To, Sp, index, Sp, To, Sp,
            baseType, Sp, To, Sp, units, Comma, Sp,
            Open, globalCompatibility, Close, Sp, Iff, Sp, Open, coboundary, Close,
            CloseBracket);
    }

    private static Formula GlobalChecksFormula() => Disp(Seq(
        LocalCountermodelFormula(), Sp, Land, Sp,
        InverseImageFormula(), Sp, Land, Sp,
        TransitionCriterionFormula(), Dot));
}
