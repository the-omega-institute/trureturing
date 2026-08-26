using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class InformationValueMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity."
            + "free_information_refinement_value_monotone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free ignorable refinement with unchanged actions cannot lower optimal value.",
        H("Information Value Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("free-information-refinement-value-is-monotone"),
            DeclarationHandle.Create(Declaration),
            H("Free information refinement cannot lower optimal value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The coarse and fine policy values use the same expectation and utility. "
                        + "The fine value additionally evaluates the post-information world and "
                        + "subtracts the information cost.")),
                Paragraph(Text(
                    "The public factor witness states concept refinement. Its remaining public "
                        + "clauses say that action sets are exactly preserved through the factor "
                        + "and every coarse candidate policy can ignore the added information by "
                        + "composition.")),
                Paragraph(Text(
                    "Lift a policy attaining the coarse optimum along the forgetting map. Exact "
                        + "action preservation makes it admissible; zero cost and the unchanged "
                        + "world make its fine value equal to the coarse optimum. Fine optimality "
                        + "then supplies the comparison."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Admissible(Formula candidates, Formula actions) =>
        Call("admissiblePolicies", candidates, actions);

    private static Formula ExpectedValue(
        Formula expectation,
        Formula concept,
        Formula world,
        Formula utility,
        Formula cost,
        Formula policy) =>
        Call("informedExpectedValue", expectation, concept, world, utility, cost, policy);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarse = F.Id("C");
        Formula fine = F.Id("D");
        Formula action = F.Id("U");
        Formula coarseConcept = Sub(F.Id("q"), coarse);
        Formula fineConcept = Sub(F.Id("q"), fine);
        Formula forget = F.Id("p");
        Formula utility = F.Id("V");
        Formula expectation = Seq(Mathbb, Grp(F.Id("E")));
        Formula world = F.Id("T");
        Formula identityWorld = Seq(Operatorname, Grp(F.Id("idWorld")));
        Formula cost = F.Id("c");
        Formula coarseActions = Sub(action, coarse);
        Formula fineActions = Sub(action, fine);
        Formula coarseCandidates = Sub(Pi, coarse);
        Formula fineCandidates = Sub(Pi, fine);
        Formula coarsePolicy = Sub(F.Id("p"), coarse);
        Formula finePolicy = Sub(F.Id("p"), fine);
        Formula evidence = F.Id("d");
        Formula state = F.Id("x");
        Formula coarseOptimal = Sub(F.Id("W"), coarse);
        Formula fineOptimal = Sub(F.Id("W"), fine);
        Formula zero = D(0);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula expectationType = Call("Concept", Arrow(stateType, real), real);
        Formula coarseConceptType = Call("Concept", stateType, coarse);
        Formula fineConceptType = Call("Concept", stateType, fine);
        Formula worldType = Arrow(fine, Arrow(stateType, stateType));
        Formula utilityType = Call("Concept", stateType, Arrow(action, real));
        Formula coarseActionsType = Arrow(coarse, Call("Set", action));
        Formula fineActionsType = Arrow(fine, Call("Set", action));
        Formula coarseCandidatesType = Call("Set", Arrow(coarse, action));
        Formula fineCandidatesType = Call("Set", Arrow(fine, action));

        Formula coarseValue = ExpectedValue(
            expectation, coarseConcept, identityWorld, utility, zero, coarsePolicy);
        Formula ignoredFinePolicy = Compose(coarsePolicy, forget);
        Formula fineValue = ExpectedValue(
            expectation, fineConcept, world, utility, cost, finePolicy);
        Formula safeguards = Seq(
            Exists, Sp, forget, Colon, Sp, fine, Sp, To, Sp, coarse, Comma, Sp,
            coarseConcept, Sp, Eq, Sp, Compose(forget, fineConcept), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, evidence, Colon, Sp, fine, Comma, Sp,
            Apply(fineActions, evidence), Sp, Eq, Sp,
            Apply(coarseActions, Apply(forget, evidence)), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, coarsePolicy, Colon, Sp, Arrow(coarse, action), Comma, Sp,
            coarsePolicy, Sp, InMacro, Sp, coarseCandidates, Sp, Rightarrow, Sp,
            ignoredFinePolicy, Sp, InMacro, Sp, fineCandidates, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, coarse, Comma, Sp, fine, Comma, Sp,
            action, Colon, Sp, type, Comma, RowBreak, Grp(),
            expectation, Colon, Sp, expectationType, Comma, Sp,
            coarseConcept, Colon, Sp, coarseConceptType, Comma, RowBreak, Grp(),
            fineConcept, Colon, Sp, fineConceptType, Comma, Sp,
            world, Colon, Sp, worldType, Comma, RowBreak, Grp(),
            utility, Colon, Sp, utilityType, Comma, Sp,
            cost, Colon, Sp, real, Comma, RowBreak, Grp(),
            coarseActions, Colon, Sp, coarseActionsType, Comma, Sp,
            fineActions, Colon, Sp, fineActionsType, Comma, RowBreak, Grp(),
            coarseCandidates, Colon, Sp, coarseCandidatesType, Comma, Sp,
            fineCandidates, Colon, Sp, fineCandidatesType, Comma, RowBreak, Grp(),
            coarseOptimal, Comma, Sp, fineOptimal, Colon, Sp, real, Comma, RowBreak, Grp(),
            cost, Sp, Eq, Sp, zero, Comma, RowBreak, Grp(),
            Forall, Sp, evidence, Colon, Sp, fine, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            Apply(Apply(world, evidence), state), Sp, Eq, Sp, state,
            Comma, RowBreak, Grp(),
            safeguards, Comma, RowBreak, Grp(),
            coarseOptimal, Sp, Eq, Sp,
            Max, Underscore, Grp(coarsePolicy, Sp, InMacro, Sp,
                Admissible(coarseCandidates, coarseActions)), Sp,
            coarseValue, Comma, RowBreak, Grp(),
            fineOptimal, Sp, Eq, Sp,
            Max, Underscore, Grp(finePolicy, Sp, InMacro, Sp,
                Admissible(fineCandidates, fineActions)), Sp,
            fineValue, RowBreak, Grp(),
            Rightarrow, Sp, fineOptimal, Sp, Geq, Sp, coarseOptimal, Dot,
            End, Grp(F.Id("gathered"))));
    }

}
