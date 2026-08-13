using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class ThreeCycleGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-state successor cycle has distinct least and greatest fixed points.",
        H("Three-Cycle Fixed-Point Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-cycle-has-fixed-point-gap"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/ThreeCycleGap.three_cycle_has_fixed_point_gap"),
                H("Least and greatest cycle solutions differ"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("lfp")),
                    Open, F.Id("threeCycleOperator"), Close, Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("gfp")),
                    Open, F.Id("threeCycleOperator"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen three-cycle theorem identifies the least fixed point with "
                        + "the empty set and the greatest fixed point with the full carrier. "
                        + "The explicit first state belongs to the latter and not the former, "
                        + "so the two fixed points are distinct.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the extremal fixed-point construction, while "
                        + "the repository supplies this concrete successor-cycle instance. "
                        + "No existing declaration states the resulting inequality.")),
                    Paragraph(Text(
                        "This continuation closes only the concrete self-reference gap. The "
                        + "separate induction and coinduction reachability interpretation "
                        + "remains outside this declaration."))),
                DescribeRole.Theorem))));
}
