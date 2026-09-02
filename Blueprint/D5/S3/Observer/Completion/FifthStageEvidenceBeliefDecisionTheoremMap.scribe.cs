using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class FifthStageEvidenceBeliefDecisionTheoremMapDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/FifthStageEvidenceBeliefDecisionTheoremMap."
            + "fifth_stage_evidence_belief_decision_theorem_map";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A typed fifth-stage map joins evidence separation, belief sufficiency, "
            + "stopping risk, Bellman optimality, and adaptive observation cost.",
        H("Fifth-Stage Evidence, Belief, and Decision Theorem Map"),
        Blocks(Describe.Lean(
            DescribeId.Create("fifth-stage-evidence-belief-decision-theorem-map"),
            DeclarationHandle.Create(Declaration),
            H("The typed components of statistical and active completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Under the named evidence-to-singularity bridge, divergent pair "
                        + "evidence yields mutually singular transcript laws and a common "
                        + "zero-error classifier.")),
                Paragraph(Text(
                    "Equal posteriors determine finite-horizon adaptive future laws and "
                        + "continuation values, while stopping in a posterior threshold "
                        + "region bounds the resulting MAP error.")),
                Paragraph(Text(
                    "For a finite discounted ordinary MDP, the Bellman operator is a "
                        + "strict contraction with a unique fixed value and every globally "
                        + "greedy stationary policy realizes that value.")),
                Paragraph(Text(
                    "A concrete three-state tree retains exact identification and strictly "
                        + "reduces expected calls. The final countermodel records that the "
                        + "abstract evidence bridge cannot be omitted.")),
                Paragraph(Text(
                    "This theorem deliberately does not identify the components with one "
                        + "closed-loop common fixed point: that sequential synthesis is not "
                        + "available in the repository or pinned Mathlib."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), law = F.Id("L");
        Formula belief = F.Id("pi"), history = F.Id("h");
        Formula otherHistory = Seq(history, Caret, Grp(F.Id("prime")));
        Formula gamma = F.Id("gamma"), epsilon = F.Id("epsilon");
        Formula bellman = F.Id("T"), value = F.Id("V");
        Formula optimalValue = Seq(value, Caret, Grp(Star));
        Formula policyValue = Seq(value, Caret, Grp(F.Id("mu")));
        Formula active = new Formula.Subscript(F.Id("C"), F.Id("adaptive"));
        Formula passive = new Formula.Subscript(F.Id("C"), F.Id("static"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("KakutaniBridge"), Sp, Land, Sp, Call("DivergentPairEvidence"),
            Sp, Rightarrow, Sp,
            Call("PairwiseSingular", law, x, y), Sp, Land, Sp,
            Call("ZeroErrorClassifier", law), Comma,
            RowBreak, Grp(),
            new Formula.Subscript(belief, history), Sp, Eq, Sp,
            new Formula.Subscript(belief, otherHistory), Sp, Rightarrow, Sp,
            Call("SameAdaptiveFutureLaws"), Sp, Land, Sp,
            Call("SameContinuationValues"), Comma,
            RowBreak, Grp(),
            Call("PosteriorThresholdStop", epsilon), Sp, Rightarrow, Sp,
            Call("MAPRisk"), Sp, Le, Sp, epsilon, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, gamma, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Call("Stochastic"), Sp, Rightarrow, Sp,
            Call("GammaContraction", bellman), Sp, Land, Sp,
            Call("UniqueFixedValue", bellman, optimalValue), Comma,
            RowBreak, Grp(),
            Call("Greedy", F.Id("mu"), optimalValue), Sp, Rightarrow, Sp,
            policyValue, Sp, Eq, Sp, optimalValue, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, epsilon, Sp, Lt, Sp,
            Frac, Grp(D(1)), Grp(D(2)),
            Sp, Rightarrow, Sp,
            Call("Exact", active), Sp, Land, Sp,
            Call("Expected", active), Sp, Eq, Sp,
            D(1), Sp, Plus, Sp, D(2), Sp, Times, Sp, epsilon,
            Sp, Lt, Sp, Call("Expected", passive), Sp, Eq, Sp, D(2), Comma,
            RowBreak, Grp(),
            Exists, Sp, Call("Countermodel"), Colon, Sp,
            Call("DivergentPairEvidence"), Sp, Land, Sp,
            new Formula.Not(Call("PairwiseSingular", law, x, y)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
