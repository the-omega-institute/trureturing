using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class BeliefMarkovUpdateDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite predictive output weights are the observed marginal, and conditioning the "
            + "same joint weight gives the canonical totalized Bayes update.",
        H("Belief Markov Update"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("output-marginal-follows-predictive-law"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "output_marginal_follows_predictive_law"),
                H("The observed marginal is the predictive output law"),
                StatementSource.FromAuthor(OutputLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mix the state-conditioned likelihood against the current finite belief. "
                        + "Marginalizing the corresponding hidden-state and output weight over "
                        + "the hidden state gives exactly that named predictive law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-next-belief-is-the-posterior-update"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "actual_next_belief_eq_posterior_update"),
                H("The actual next belief is the canonical posterior update"),
                StatementSource.FromAuthor(NextBeliefFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conditioning the same hidden-state and output weight at an observed output "
                        + "has the numerator and normalizer of the existing posteriorUpdate. "
                        + "Thus the history-side next belief and belief-side update coincide."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("predictive-null-output-uses-the-zero-posterior"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_predictive_mass_update_is_zero"),
                H("A predictive-null output receives the zero posterior"),
                StatementSource.FromAuthor(ZeroVersionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source allows any conditional version on a predictive-null output. "
                        + "The repository chooses a concrete version: NNReal division by zero "
                        + "returns zero, so every coordinate of the updated belief is zero."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula OutputLawFormula()
    {
        Formula thetaType = Theta;
        Formula outputType = F.Id("Y");
        Formula nnreal = F.Id("NNReal");
        Formula likelihood = F.Id("L");
        Formula belief = F.Id("pi");
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        Formula jointWeight = JointWeight(likelihood, belief, state, output);
        Formula marginal = Seq(
            Open, output, Close, Sp, Mapsto, Sp,
            Call("historyMass", jointWeight, output));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, thetaType, Comma, Sp, outputType, Colon, Sp, F.Id("Type"),
            Comma, RowBreak, Grp(),
            Call("Fintype", thetaType), Comma, Sp,
            likelihood, Colon, Sp, Arrow(thetaType, Arrow(outputType, nnreal)),
            Comma, RowBreak, Grp(),
            belief, Colon, Sp, Arrow(thetaType, nnreal), Comma, RowBreak, Grp(),
            marginal, Sp, Eq, Sp, Call("predictiveOutputLaw", likelihood, belief), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NextBeliefFormula()
    {
        Formula thetaType = Theta;
        Formula outputType = F.Id("Y");
        Formula nnreal = F.Id("NNReal");
        Formula likelihood = F.Id("L");
        Formula belief = F.Id("pi");
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        Formula jointWeight = JointWeight(likelihood, belief, state, output);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, thetaType, Comma, Sp, outputType, Colon, Sp, F.Id("Type"),
            Comma, RowBreak, Grp(),
            Call("Fintype", thetaType), Comma, Sp,
            likelihood, Colon, Sp, Arrow(thetaType, Arrow(outputType, nnreal)),
            Comma, RowBreak, Grp(),
            belief, Colon, Sp, Arrow(thetaType, nnreal), Comma, Sp,
            output, Colon, Sp, outputType, Comma, RowBreak, Grp(),
            Call("posterior", jointWeight, output), Sp, Eq, Sp,
            Call("posteriorUpdate", likelihood, belief, output), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ZeroVersionFormula()
    {
        Formula thetaType = Theta;
        Formula outputType = F.Id("Y");
        Formula nnreal = F.Id("NNReal");
        Formula likelihood = F.Id("L");
        Formula belief = F.Id("pi");
        Formula output = F.Id("y");
        Formula state = F.Id("x");
        Formula zeroBelief = Seq(Open, state, Close, Sp, Mapsto, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, thetaType, Comma, Sp, outputType, Colon, Sp, F.Id("Type"),
            Comma, RowBreak, Grp(),
            Call("Fintype", thetaType), Comma, Sp,
            likelihood, Colon, Sp, Arrow(thetaType, Arrow(outputType, nnreal)),
            Comma, RowBreak, Grp(),
            belief, Colon, Sp, Arrow(thetaType, nnreal), Comma, Sp,
            output, Colon, Sp, outputType, Comma, RowBreak, Grp(),
            Apply(Call("predictiveOutputLaw", likelihood, belief), output), Sp,
            Eq, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
            Call("posteriorUpdate", likelihood, belief, output), Sp, Eq, Sp,
            zeroBelief, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula JointWeight(
        Formula likelihood,
        Formula belief,
        Formula state,
        Formula output) =>
        Seq(
            Open, state, Comma, Sp, output, Close, Sp, Mapsto, Sp,
            Apply(belief, state), Sp, Times, Sp, Apply(likelihood, state, output));
}
