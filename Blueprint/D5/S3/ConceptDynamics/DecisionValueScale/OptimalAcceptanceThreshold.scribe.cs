using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class OptimalAcceptanceThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary expected-loss comparison is equivalent to the optimal acceptance threshold.",
        H("Optimal Acceptance Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("optimal-acceptance-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold."
                        + "optimal_acceptance_threshold"),
                H("Acceptance threshold"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The posterior probability p and both error costs are real, with "
                            + "strictly positive false-positive and false-negative costs.")),
                    Paragraph(Text(
                        "Accepting has expected loss (1-p)c_FP, while rejecting has expected "
                            + "loss p c_FN. Their direct comparison is equivalent to p reaching "
                            + "the displayed cost threshold.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found no exact theorem combining "
                            + "this source loss comparison with the threshold equivalence."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula posterior = F.Id("p");
        Formula falsePositiveCost = Subscript(F.Id("c"), F.Id("FP"));
        Formula falseNegativeCost = Subscript(F.Id("c"), F.Id("FN"));
        Formula acceptLoss = Seq(
            Open, D(1), Sp, Minus, Sp, posterior, Close, Sp, falsePositiveCost);
        Formula rejectLoss = Seq(posterior, Sp, falseNegativeCost);
        Formula threshold = Seq(
            Frac,
            Grp(falsePositiveCost),
            Grp(falsePositiveCost, Sp, Plus, Sp, falseNegativeCost));

        return Disp(Seq(
            Forall, Sp, posterior, Comma, Sp, falsePositiveCost, Comma, Sp,
            falseNegativeCost, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Sp, Lt, Sp, falsePositiveCost, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, falseNegativeCost, Sp, Rightarrow, Sp,
            Open,
            acceptLoss, Sp, Leq, Sp, rejectLoss, Sp, Iff, Sp,
            posterior, Sp, Geq, Sp, threshold,
            Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
