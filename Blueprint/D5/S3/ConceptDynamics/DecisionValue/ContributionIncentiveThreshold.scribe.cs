using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class ContributionIncentiveThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary contribution is dominant exactly at the source compensation threshold.",
        H("Contribution Incentive Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contribution-incentive-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold."
                        + "contribution_incentive_threshold"),
                H("Contribution becomes dominant at the compensation threshold"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are n at least two agents and each binary profile records whether "
                            + "each agent contributes. The aggregate is constructed from the "
                            + "selected action and the finite sum over every other agent.")),
                    Paragraph(Text(
                        "The compensated utility is the common per-agent benefit b/n times total "
                            + "contribution, minus the contributor's cost c, plus compensation rho. "
                            + "The source restrictions b greater than c greater than b/n are public.")),
                    Paragraph(Text(
                        "Updating one agent from non-contribution to contribution changes utility "
                            + "by b/n-c+rho, independently of the other actions. Hence weak dominance "
                            + "is equivalent to rho at least c-b/n and strict dominance follows "
                            + "above that threshold.")),
                    Paragraph(Text(
                        "The public conclusion also states that c-b/n is the least member of the "
                            + "set of compensations inducing weak dominance. Funding, allocation, "
                            + "and fairness are identified by the source as separate normative "
                            + "questions and are not promoted to universal mathematical claims.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found no exact theorem packaging "
                            + "the source payoff construction and all three threshold clauses."))),
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

    private static Formula Threshold(Formula benefit, Formula cost, Formula agents) =>
        Seq(cost, Sp, Minus, Sp, Frac, Grp(benefit), Grp(agents));

    private static Formula TheoremFormula()
    {
        Formula agents = F.Id("n");
        Formula benefit = F.Id("b");
        Formula cost = F.Id("c");
        Formula compensation = Tau;
        Formula candidate = Rho;
        Formula agent = F.Id("i");
        Formula other = F.Id("j");
        Formula profile = F.Id("a");
        Formula action = Subscript(profile, other);
        Formula threshold = Threshold(benefit, cost, agents);
        Formula weak = Call("Weak", compensation);
        Formula strict = Call("Strict", compensation);
        Formula candidateWeak = Call("Weak", candidate);
        Formula payoffDefinition = Seq(
            Call("payoff", candidate, agent, profile), Sp, Eq, Sp,
            Frac, Grp(benefit), Grp(agents), Sp,
            Sum, Underscore, Grp(other, Sp, InMacro, Sp, Call("Fin", agents)), Sp,
            action, Sp, Minus, Sp, cost, Sp, Subscript(profile, agent), Sp,
            Plus, Sp, candidate, Sp, Subscript(profile, agent));
        Formula profileType = Seq(Call("Fin", agents), Sp, To, Sp,
            OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);
        Formula weakDefinition = Seq(
            Call("Weak", candidate), Sp, Iff, Sp,
            Forall, Sp, agent, Sp, InMacro, Sp, Call("Fin", agents), Comma, Sp,
            profile, Colon, Sp, profileType, Comma, Sp,
            Call("payoff", candidate, agent, Call("update", profile, agent, D(0))),
            Sp, Leq, Sp,
            Call("payoff", candidate, agent, Call("update", profile, agent, D(1))));
        Formula strictDefinition = Seq(
            Call("Strict", candidate), Sp, Iff, Sp,
            Forall, Sp, agent, Sp, InMacro, Sp, Call("Fin", agents), Comma, Sp,
            profile, Colon, Sp, profileType, Comma, Sp,
            Call("payoff", candidate, agent, Call("update", profile, agent, D(0))),
            Sp, Lt, Sp,
            Call("payoff", candidate, agent, Call("update", profile, agent, D(1))));
        Formula least = Call("IsLeast", Seq(
            OpenBrace, candidate, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Sp,
            Mid, Sp, candidateWeak, CloseBrace), threshold);

        return Disp(Seq(
            agents, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(2), Sp, Leq, Sp, agents, Comma, Sp,
            benefit, Comma, Sp, cost, Comma, Sp, compensation,
            Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            benefit, Sp, Gt, Sp, cost, Sp, Gt, Sp,
            Frac, Grp(benefit), Grp(agents), Comma, RowBreak, Grp(),
            payoffDefinition, Comma, RowBreak, Grp(),
            weakDefinition, Comma, RowBreak, Grp(),
            strictDefinition, RowBreak, Grp(),
            Rightarrow, Sp,
            Open, weak, Sp, Iff, Sp, compensation, Sp, Geq, Sp, threshold, Close,
            Sp, Land, RowBreak, Grp(),
            Open, compensation, Sp, Gt, Sp, threshold, Sp, Rightarrow, Sp,
            strict, Close, Sp, Land, RowBreak, Grp(),
            least, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
