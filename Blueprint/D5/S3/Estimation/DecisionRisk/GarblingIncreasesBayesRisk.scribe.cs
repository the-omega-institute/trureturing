using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class GarblingIncreasesBayesRiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blackwell dominance is reflexive and transitive, includes measurable deterministic "
            + "post-processing, and its garblings cannot improve optimal Bayes risk.",
        H("Garbling Increases Bayes Risk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blackwell-dominance-is-reflexive"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk."
                        + "blackwellDominates_refl"),
                H("Blackwell dominance is reflexive"),
                StatementSource.FromAuthor(ReflexivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every experiment dominates itself because the identity kernel is a "
                            + "Markov kernel and garbling by that kernel leaves the experiment "
                            + "unchanged.")),
                    Paragraph(Text(
                        "Thus the experiment itself is recovered by an admissible garbling, "
                            + "which supplies the witness required by Blackwell dominance."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("blackwell-dominance-is-transitive"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk."
                        + "blackwellDominates_trans"),
                H("Blackwell dominance is transitive"),
                StatementSource.FromAuthor(TransitivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose Q is obtained from P through one Markov garbling and R is "
                            + "obtained from Q through another. Composing the two garbling "
                            + "kernels gives a Markov kernel directly from the output of P to "
                            + "the output of R.")),
                    Paragraph(Text(
                        "Associativity of kernel composition identifies this composite "
                            + "garbling with R, so P Blackwell-dominates R."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("measurable-maps-are-blackwell-garblings"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk."
                        + "blackwellDominates_map"),
                H("Measurable maps are Blackwell garblings"),
                StatementSource.FromAuthor(DeterministicMapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A measurable transformation of the observation space determines a "
                            + "deterministic Markov kernel. Applying that kernel after an "
                            + "experiment is exactly the mapped experiment.")),
                    Paragraph(Text(
                        "Consequently every measurable deterministic post-processing of an "
                            + "experiment is a Blackwell garbling of the original experiment."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("garbling-cannot-decrease-optimal-bayes-risk"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk."
                        + "bayesRisk_le_of_blackwellDominates"),
                H("Garbling cannot decrease optimal Bayes risk"),
                StatementSource.FromAuthor(BayesRiskMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If Q is obtained by applying a Markov garbling to P, then every "
                            + "decision procedure based on Q can also be run after observing P: "
                            + "first garble the observation and then apply that procedure.")),
                    Paragraph(Text(
                        "Taking the infimum over all Markov decision rules therefore gives no "
                            + "larger Bayes risk for P than for Q. The comparison holds for every "
                            + "ENNReal-valued loss and every measure used as the prior."))),
                DescribeRole.Theorem))));

    private static Formula ReflexivityFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula experiment = F.Id("P");

        return Disp(Seq(
            Forall, Sp, experiment, Colon, Sp, Kernel(parameter, observation), Comma, Sp,
            Dominates(experiment, experiment), Dot));
    }

    private static Formula TransitivityFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula firstOutput = new Formula.Subscript(F.Id("X"), D(1));
        Formula secondOutput = new Formula.Subscript(F.Id("X"), D(2));
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula third = F.Id("R");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, first, Colon, Sp, Kernel(parameter, observation), Comma, Sp,
            second, Colon, Sp, Kernel(parameter, firstOutput), Comma, Sp,
            third, Colon, Sp, Kernel(parameter, secondOutput), Comma, RowBreak, Grp(),
            Dominates(first, second), Sp, Land, Sp, Dominates(second, third),
            Sp, Rightarrow, RowBreak, Grp(),
            Dominates(first, third), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DeterministicMapFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula output = new Formula.Subscript(F.Id("X"), D(1));
        Formula experiment = F.Id("P");
        Formula function = F.Id("f");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, experiment, Colon, Sp, Kernel(parameter, observation), Comma, Sp,
            function, Colon, Sp, observation, Sp, To, Sp, output, Comma, RowBreak, Grp(),
            Call("Measurable", function), Sp, Rightarrow, RowBreak, Grp(),
            Dominates(experiment, Call("map", experiment, function)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BayesRiskMonotonicityFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula output = new Formula.Subscript(F.Id("X"), D(1));
        Formula decision = F.Id("Y");
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula loss = Ell;
        Formula prior = Pi;

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, first, Colon, Sp, Kernel(parameter, observation), Comma, Sp,
            second, Colon, Sp, Kernel(parameter, output), Comma, RowBreak, Grp(),
            Dominates(first, second), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, loss, Colon, Sp, parameter, Sp, To, Sp, decision, Sp, To, Sp,
            F.Id("ENNReal"), Comma, Sp,
            prior, Colon, Sp, Call("Measure", parameter), Comma, RowBreak, Grp(),
            BayesRisk(loss, first, prior), Sp, Leq, Sp,
            BayesRisk(loss, second, prior), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Kernel(Formula source, Formula target) =>
        Call("Kernel", source, target);

    private static Formula Dominates(Formula first, Formula second) =>
        Call("BlackwellDominates", first, second);

    private static Formula BayesRisk(Formula loss, Formula experiment, Formula prior) =>
        Call("bayesRisk", loss, experiment, prior);
}
