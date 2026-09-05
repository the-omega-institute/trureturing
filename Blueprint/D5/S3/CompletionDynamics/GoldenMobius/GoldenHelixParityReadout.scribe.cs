using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenHelixParityReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden helix orientation is flipped at odd depth and restored at even depth while the lifted state continues to advance.",
        H("Golden Helix Parity Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-helix-odd-orientation-breaking"),
                DeclarationHandle.Create(Prefix + "golden_helix_odd_orientation_breaking"),
                H("Odd helix depth breaks the orientation readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Odd")), Open, F.Id("n"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("orientation")),
                    Open, Operatorname, Grp(F.Id("goldenHelixStep")), Caret, F.Id("n"),
                    Open, F.Id("state"), Close, Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("orientation")), Open, F.Id("state"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every odd iterate of the golden helix lies on the opposite Boolean orientation sheet.")),
                    Paragraph(Text(
                        "The result concerns the orientation observer and makes no universal claim about parity in arbitrary projection towers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-step-orientation-complete-state-distinct"),
                DeclarationHandle.Create(Prefix
                    + "golden_helix_two_step_orientation_complete_state_distinct"),
                H("Two steps complete orientation without returning the state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Operatorname, Grp(F.Id("orientation")),
                    Open, Operatorname, Grp(F.Id("goldenHelixStep")), Caret, D(2),
                    Open, F.Id("state"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("orientation")), Open, F.Id("state"), Close,
                    Close,
                    Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("goldenHelixStep")), Caret, D(2),
                    Open, F.Id("state"), Close,
                    Sp, Neq, Sp, F.Id("state"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two helix steps restore the orientation coordinate because the orientation flip is involutive.")),
                    Paragraph(Text(
                        "The completion is observer-relative: the level coordinate has advanced twice, so the complete helix state is distinct."))),
                DescribeRole.Theorem))));
}
