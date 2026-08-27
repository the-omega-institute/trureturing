using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class DominantStrategyDirectificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dominant strategies induce truthful dominance in the direct mechanism.",
        H("Dominant-Strategy Directification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dominant-strategy-directification"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/DominantStrategyDirectification."
                        + "dominant_strategy_directification"),
                H("Truthful reports remain dominant after directification"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Agents are indexed by Fin n and may have different type and message "
                            + "spaces. The original mechanism consumes a dependent message profile, "
                            + "and each utility evaluates outcomes at one agent's true type.")),
                    Paragraph(Text(
                        "The public hypothesis says each strategy weakly dominates every alternative "
                            + "own message for every profile of the other messages. The direct "
                            + "mechanism is publicly constructed by applying all strategies to the "
                            + "reported type profile before invoking the original mechanism.")),
                    Paragraph(Text(
                        "Updating one reported type and then applying the strategy family equals "
                            + "updating the induced message profile at that agent. The original "
                            + "dominance inequality therefore applies directly, proving truthful "
                            + "reporting weakly dominates every alternative report.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact directification "
                            + "theorem. The proof directly applies the pinned coordinate-update "
                            + "lemmas for the dependent profiles."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Apply(
        Formula function, Formula first, Formula second, Formula third) =>
        Seq(function, Open, first, Comma, Sp, second, Comma, Sp, third, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula agents = F.Id("n");
        Formula agent = F.Id("i");
        Formula otherAgent = F.Id("j");
        Formula typeFamily = F.Id("T");
        Formula messageFamily = F.Id("M");
        Formula outcome = F.Id("O");
        Formula mechanism = F.Id("G");
        Formula directMechanism = F.Id("D");
        Formula strategy = F.Id("S");
        Formula utility = F.Id("U");
        Formula trueType = F.Id("t");
        Formula messages = F.Id("m");
        Formula alternativeMessage = F.Id("a");
        Formula reports = F.Id("r");
        Formula alternativeReport = F.Id("q");
        Formula finAgents = Call("Fin", agents);
        Formula typeProfile = Seq(
            Prod, Underscore, Grp(agent, Sp, InMacro, Sp, finAgents), Sp,
            Apply(typeFamily, agent));
        Formula messageProfile = Seq(
            Prod, Underscore, Grp(agent, Sp, InMacro, Sp, finAgents), Sp,
            Apply(messageFamily, agent));
        Formula strategyAtTruth = Apply(strategy, agent, trueType);
        Formula originalTruthfulOutcome = Apply(mechanism,
            Call("update", messages, agent, strategyAtTruth));
        Formula originalAlternativeOutcome = Apply(mechanism,
            Call("update", messages, agent, alternativeMessage));
        Formula originalDominance = Seq(
            Forall, Sp, agent, Sp, InMacro, Sp, finAgents, Comma, Sp,
            trueType, Sp, InMacro, Sp, Apply(typeFamily, agent), Comma, Sp,
            messages, Sp, InMacro, Sp, messageProfile, Comma, Sp,
            alternativeMessage, Sp, InMacro, Sp, Apply(messageFamily, agent), Comma, Sp,
            Apply(utility, agent, trueType, originalTruthfulOutcome), Sp, Geq, Sp,
            Apply(utility, agent, trueType, originalAlternativeOutcome));
        Formula directDefinition = Seq(
            directMechanism, Colon, Sp, Arrow(typeProfile, outcome), Comma, Sp,
            Apply(directMechanism, Seq(reports, Colon, Sp, typeProfile)),
            Sp, Colon, Eq, Sp,
            Apply(mechanism, Seq(
                LambdaLower, Sp, otherAgent, Colon, Sp, finAgents, Sp, Mapsto, Sp,
                Apply(strategy, otherAgent, Apply(reports, otherAgent)))));
        Formula directTruthfulOutcome = Apply(directMechanism,
            Call("update", reports, agent, trueType));
        Formula directAlternativeOutcome = Apply(directMechanism,
            Call("update", reports, agent, alternativeReport));
        Formula directDominance = Seq(
            Forall, Sp, agent, Sp, InMacro, Sp, finAgents, Comma, Sp,
            trueType, Sp, InMacro, Sp, Apply(typeFamily, agent), Comma, Sp,
            reports, Sp, InMacro, Sp, typeProfile, Comma, Sp,
            alternativeReport, Sp, InMacro, Sp, Apply(typeFamily, agent), Comma, Sp,
            Apply(utility, agent, trueType, directTruthfulOutcome), Sp, Geq, Sp,
            Apply(utility, agent, trueType, directAlternativeOutcome));

        return Disp(Seq(
            Forall, Sp, agents, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            typeFamily, Comma, Sp, messageFamily, Colon, Sp,
            Arrow(finAgents, F.Id("Type")), Comma, Sp,
            outcome, Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            mechanism, Colon, Sp, Arrow(messageProfile, outcome), Comma, Sp,
            Forall, Sp, agent, Sp, InMacro, Sp, finAgents, Comma, Sp,
            Subscript(strategy, agent), Colon, Sp,
            Arrow(Apply(typeFamily, agent), Apply(messageFamily, agent)), Comma,
            RowBreak, Grp(),
            Forall, Sp, agent, Sp, InMacro, Sp, finAgents, Comma, Sp,
            Subscript(utility, agent), Colon, Sp,
            Arrow(Apply(typeFamily, agent),
                Arrow(outcome, Seq(Mathbb, Grp(F.Id("R"))))), Comma, RowBreak, Grp(),
            Grp(originalDominance), Sp, Rightarrow, RowBreak, Grp(),
            directDefinition, Comma, RowBreak, Grp(),
            Grp(directDominance), Dot));
    }
}
