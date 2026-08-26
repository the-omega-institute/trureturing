using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class FiniteHorizonValueFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible abstract dynamics factor every finite-horizon Bellman value.",
        H("Finite-Horizon Value Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-horizon-value-factorization"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization."
                    + "finite_horizon_value_factorization"),
            H("Every finite-horizon value factors through the abstraction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The micro and macro state carriers share one finite nonempty action carrier. "
                        + "Their transitions commute with the concept map, while the stage reward "
                        + "and terminal value are evaluations of their macro counterparts.")),
                Paragraph(Text(
                    "The imported finiteHorizonValue primitive constructs both Bellman recurrences. "
                        + "The terminal equality starts the induction, and compatibility identifies "
                        + "every action score before the finite maxima are compared."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula micro = F.Id("X");
        Formula macro = F.Id("Z");
        Formula action = F.Id("U");
        Formula concept = F.Id("C");
        Formula microStep = F.Id("F");
        Formula macroStep = F.Id("G");
        Formula microReward = F.Id("r");
        Formula macroReward = F.Id("rbar");
        Formula microTerminal = F.Id("q");
        Formula macroTerminal = F.Id("qbar");
        Formula horizon = F.Id("n");
        Formula state = F.Id("x");
        Formula selectedAction = F.Id("u");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));

        Formula transitionLaw = Seq(
            Open, Forall, Sp, Typed(selectedAction, action), Comma, Sp,
            Typed(state, micro), Comma, Sp,
            Apply(concept, Apply(microStep, selectedAction, state)), Sp, Eq, Sp,
            Apply(macroStep, selectedAction, Apply(concept, state)), Close);
        Formula rewardLaw = Seq(
            Open, Forall, Sp, Typed(state, micro), Comma, Sp,
            Typed(selectedAction, action), Comma, Sp,
            Apply(microReward, state, selectedAction), Sp, Eq, Sp,
            Apply(macroReward, Apply(concept, state), selectedAction), Close);
        Formula terminalLaw = Seq(
            Open, Forall, Sp, Typed(state, micro), Comma, Sp,
            Apply(microTerminal, state), Sp, Eq, Sp,
            Apply(macroTerminal, Apply(concept, state)), Close);
        Formula microValue = Apply(
            F.Id("finiteHorizonValue"), microStep, microReward, microTerminal, horizon);
        Formula macroValue = Apply(
            F.Id("finiteHorizonValue"), macroStep, macroReward, macroTerminal, horizon);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(micro, Comma, Sp, macro, Comma, Sp, action), type),
            Comma, RowBreak, Grp(),
            Typed(concept, Apply(F.Id("Concept"), micro, macro)), Comma, Sp,
            Typed(microStep, Arrow(action, Arrow(micro, micro))), Comma, RowBreak, Grp(),
            Typed(macroStep, Arrow(action, Arrow(macro, macro))), Comma, Sp,
            Typed(microReward, Arrow(micro, Arrow(action, real))), Comma, RowBreak, Grp(),
            Typed(macroReward, Arrow(macro, Arrow(action, real))), Comma, Sp,
            Typed(microTerminal, Arrow(micro, real)), Comma, RowBreak, Grp(),
            Typed(macroTerminal, Arrow(macro, real)), Comma, RowBreak, Grp(),
            Apply(F.Id("Fintype"), action), Sp, Land, Sp,
            Apply(F.Id("Nonempty"), action), Sp, Land, RowBreak, Grp(),
            transitionLaw, Sp, Land, RowBreak, Grp(),
            rewardLaw, Sp, Land, RowBreak, Grp(),
            terminalLaw, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(horizon, natural), Comma, Sp,
            microValue, Sp, Eq, Sp, macroValue, Sp, Circ, Sp, concept, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
