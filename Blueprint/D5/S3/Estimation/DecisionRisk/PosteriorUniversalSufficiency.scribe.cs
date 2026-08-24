using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class PosteriorUniversalSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal finite-state posteriors remain equal under a common observation update and "
            + "give equal normalized one-step Bayes values for every action type and real loss.",
        H("Universal Sufficiency of the Posterior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("posterior-updates-depend-only-on-the-current-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency."
                        + "posterior_update_depends_only_on_posterior"),
                H("A posterior update depends only on the current posterior"),
                StatementSource.FromAuthor(PosteriorUpdateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A common observation likelihood updates a finite-state posterior by "
                            + "multiplying each state weight by its likelihood and normalizing "
                            + "the resulting weights.")),
                    Paragraph(Text(
                        "If two current posteriors are the same function on the state space, "
                            + "then every updated numerator and the shared normalizing sum are "
                            + "the same for any observation. The updated posteriors therefore "
                            + "agree, including when the normalizer is zero because division is "
                            + "totalized."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("equal-posteriors-have-equal-conditional-bayes-values"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency."
                        + "posterior_universal_sufficiency"),
                H("Equal posteriors have every conditional Bayes value in common"),
                StatementSource.FromAuthor(UniversalSufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A history determines a totalized posterior by normalizing its finite "
                            + "nonnegative state weights. A zero-mass history yields the zero "
                            + "posterior, so the statement covers zero-mass histories without a "
                            + "separate positivity assumption.")),
                    Paragraph(Text(
                        "For any action type and real loss, equal posterior functions give the "
                            + "same expected loss at every action. Their sets of attainable "
                            + "conditional risks are therefore identical, and taking the real "
                            + "infimum gives equal conditional Bayes values.")),
                    Paragraph(Text(
                        "The conclusion is universal over action types and one-step losses. It "
                            + "establishes posterior sufficiency for these normalized conditional "
                            + "values, but does not assert a result about arbitrary-horizon "
                            + "experiment policies."))),
                DescribeRole.Theorem))));

    private static Formula PosteriorUpdateFormula()
    {
        Formula parameter = Theta;
        Formula observationType = F.Id("O");
        Formula likelihood = F.Id("L");
        Formula prior = F.Id("p");
        Formula otherPrior = F.Id("pPrime");
        Formula observation = F.Id("y");
        Formula nnreal = Seq(
            Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, Sp, D(0)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, parameter, Comma, Sp, observationType, Comma, Sp,
            Call("Finite", parameter), Comma, RowBreak, Grp(),
            likelihood, Colon, Sp,
            parameter, Sp, Times, Sp, observationType, Sp, To, Sp, nnreal,
            Comma, RowBreak, Grp(),
            prior, Comma, Sp, otherPrior, Colon, Sp,
            parameter, Sp, To, Sp, nnreal, Comma, Sp,
            observation, Colon, Sp, observationType, Comma, RowBreak, Grp(),
            prior, Sp, Eq, Sp, otherPrior, Sp, Rightarrow, Sp,
            Call("posteriorUpdate", likelihood, prior, observation), Sp, Eq, RowBreak, Grp(),
            Call("posteriorUpdate", likelihood, otherPrior, observation), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula UniversalSufficiencyFormula()
    {
        Formula parameter = Theta;
        Formula historyType = F.Id("H");
        Formula joint = F.Id("j");
        Formula history = F.Id("h");
        Formula otherHistory = F.Id("hPrime");
        Formula actionType = F.Id("A");
        Formula loss = Ell;
        Formula nnreal = Seq(
            Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, Sp, D(0)));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, parameter, Comma, Sp, historyType, Comma, Sp,
            Call("Finite", parameter), Comma, RowBreak, Grp(),
            joint, Colon, Sp,
            parameter, Sp, Times, Sp, historyType, Sp, To, Sp, nnreal,
            Comma, Sp, history, Comma, Sp, otherHistory, Colon, Sp, historyType,
            Comma, RowBreak, Grp(),
            Call("posterior", joint, history), Sp, Eq, Sp,
            Call("posterior", joint, otherHistory), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, actionType, Comma, Sp,
            loss, Colon, Sp,
            parameter, Sp, Times, Sp, actionType, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            Call("conditionalBayesValue", joint, history, loss), Sp, Eq, RowBreak, Grp(),
            Call("conditionalBayesValue", joint, otherHistory, loss), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
