using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class InterpretationFixedPointDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interpretation fixed points are relative to context; context variation can change "
            + "them, while objectivity carries an invariant-factor proof.",
        H("Context-Relative Interpretation Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conceptual-equivalence-and-stability"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "conceptual_equivalence_and_stability_reach_fixed_point"),
                H("Conceptual equivalence and stable interpretation reach a fixed point"),
                StatementSource.FromAuthor(RelativeFixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a text, reader-admission policy, background, evaluation goal, and "
                            + "interpretation rule. If the next concept stage is conceptually "
                            + "equivalent to the current stage and both stages have the same "
                            + "interpreted result in that context, the stage satisfies the "
                            + "definition of a relative interpretation fixed point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contextual-fixed-points-can-differ"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "context_parameters_can_select_distinct_fixed_points"),
                H("Context parameters can select distinct fixed meanings"),
                StatementSource.FromAuthor(ContextDependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A two-context finite model holds the text and interpretation rule fixed "
                            + "while changing reader admission, background, and evaluation goal. "
                            + "The selected fixed meaning records those three parameters, so the "
                            + "two contextual fixed meanings are unequal.")),
                    Paragraph(Text(
                        "This is an existential witness for the source word 'may': context "
                            + "variation can produce different fixed points. It does not claim "
                            + "that every pair of contexts must disagree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("objective-claim-requires-invariant-factor"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "objective_claim_requires_invariant_common_factor"),
                H("Objectivity requires an invariant common factor"),
                StatementSource.FromAuthor(InvariantFactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An objective interpretation claim is proof-carrying. It consists of a "
                            + "proposed factor value and a proof that every contextual fixed "
                            + "meaning maps to that same value. The theorem exposes exactly this "
                            + "invariant common factor.")),
                    Paragraph(Text(
                        "Together the three declarations cover every independent source clause: "
                            + "the relative fixed-point definition, possible contextual "
                            + "nonuniqueness, and the invariant-factor obligation for objective "
                            + "interpretation. No source clause is claimed beyond these forms."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula RelativeFixedPointFormula()
    {
        Formula context = Kappa;
        Formula current = new Formula.Subscript(F.Id("C"), F.Id("n"));
        Formula next = new Formula.Subscript(
            F.Id("C"), Seq(F.Id("n"), Plus, D(1)));
        Formula interpretation = new Formula.Subscript(F.Id("I"), context);

        return Disp(Seq(
            Call("ConceptEquivalent", next, current), Sp, Land, Sp,
            interpretation, Open, next, Close, Sp, Eq, Sp,
            interpretation, Open, current, Close, Sp, Rightarrow, Sp,
            Call("RelativeFixedPoint", context, F.Id("n")), Dot));
    }

    private static Formula ContextDependenceFormula()
    {
        Formula baseline = new Formula.Subscript(Kappa, Seq(D(0)));
        Formula alternate = new Formula.Subscript(Kappa, Seq(D(1)));
        Formula baselineMeaning = new Formula.Subscript(F.Id("m"), Seq(D(0)));
        Formula alternateMeaning = new Formula.Subscript(F.Id("m"), Seq(D(1)));

        return Disp(Seq(
            Call("sameTextAndRule", baseline, alternate), Sp, Land, Sp,
            Call("differentAdmissionBackgroundGoal", baseline, alternate),
            Sp, Land, Esc,
            Call("FixedMeaning", baseline, baselineMeaning), Sp, Land, Sp,
            Call("FixedMeaning", alternate, alternateMeaning), Sp, Land, Esc,
            baselineMeaning, Sp, Neq, Sp, alternateMeaning, Dot));
    }

    private static Formula InvariantFactorFormula()
    {
        Formula fixedMeaning = F.Id("F");
        Formula factor = F.Id("q");
        Formula context = Kappa;
        Formula meaning = F.Id("m");
        Formula common = F.Id("a");

        return Disp(Seq(
            Call("ObjectiveClaim", fixedMeaning, factor), Sp, Rightarrow, Sp,
            Exists, Sp, common, Comma, Esc,
            Forall, Sp, context, Comma, Sp, meaning, Comma, Esc,
            Call("FixedMeaning", context, meaning), Sp, Rightarrow, Sp,
            factor, Open, meaning, Close, Sp, Eq, Sp, common, Dot));
    }
}
