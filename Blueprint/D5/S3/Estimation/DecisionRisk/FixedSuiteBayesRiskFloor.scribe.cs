using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class FixedSuiteBayesRiskFloorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A learner that receives only a fixed finite observation suite cannot beat the suite's Bayes-risk floor by iterating.",
        H("Fixed-Suite Bayes-Risk Floor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-suite-learners-remain-above-the-bayes-risk-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor."
                    + "fixed_suite_bayes_risk_floor"),
                H("Every fixed-suite learner remains above the Bayes-risk floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("k"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Markov")), Open,
                    F.Id("P"), Underscore, Grp(F.Id("k")), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("bayesRisk")), Open,
                    Ell, Comma, Sp, F.Id("T"), Underscore, Grp(F.Id("m")),
                    Comma, Sp, Pi, Close,
                    Sp, Le, Sp,
                    Operatorname, Grp(F.Id("avgRisk")), Open,
                    Ell, Comma, Sp, F.Id("T"), Underscore, Grp(F.Id("m")),
                    Comma, Sp, F.Id("P"), Underscore, Grp(F.Id("k")),
                    Comma, Sp, Pi, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observation channel T has output type Fin m to X, so every observation "
                        + "is an m-entry suite. The same channel is used at every natural-numbered "
                        + "round. Each P indexed by k is a Markov kernel from that suite to a deployed "
                        + "decision, which models internal randomization without giving the learner "
                        + "a direct input from the hidden task parameter.")),
                    Paragraph(Text(
                        "Mathlib defines average risk by composing the observation channel with the "
                        + "learner kernel and integrating the loss against the prior. It defines Bayes "
                        + "risk as the infimum of those average risks over all Markov estimators. The "
                        + "displayed inequality is therefore the upstream Bayes-risk lower bound, "
                        + "specialized only enough to retain the fixed suite size and round index.")),
                    Paragraph(Text(
                        "This closes only the starvation lower-bound clause. The conditional-mode "
                        + "lower bound on unmeasured mass, the fresh-sample comparison with k times m "
                        + "observations, the later qualifications, and the empirical interpretation "
                        + "remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
