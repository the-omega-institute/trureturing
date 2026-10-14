using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteLocalRowCacheDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteLocalRowCache.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checked local row transitions preserve original assignments.",
        H("Checked local row transitions preserve original assignments."),
        Blocks(
            Paragraph(Text("The generic state retains a row index and a complete earned action. Its association predicate compares the full indexed row assignment with the action on the current actual partial assignment. The transition checker, update law, and composition law earn the new association; original row bounds and score invariance then give the actual event lower bound. The live EJM cache consumer must supply all those proofs and complete global acceptance.")),
            Describe.Lean(DescribeId.Create("associated"),
                DeclarationHandle.Create(Prefix + "Associated"),
                H("Full original-row association"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality concerns the entire indexed row assignment and the actual partial-event function after its earned action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checktransition"),
                DeclarationHandle.Create(Prefix + "checkTransition"),
                H("Check the complete proposed original update"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance compares the next complete row assignment with the proposed next action on the original updated row assignment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"),
                DeclarationHandle.Create(Prefix + "step"),
                H("Compose the new action with the old earned action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The old action transports the original coordinate and outcome to the indexed row before the next transition is queried."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-step-associated"),
                DeclarationHandle.Create(Prefix + "checked_step_associated"),
                H("Accepted transitions preserve the original actual-context association"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assignment equality follows from the previous association, checked complete update, and proved update and composition laws."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("associated-lower-bound"),
                DeclarationHandle.Create(Prefix + "associated_lower_bound"),
                H("Original accepted row bounds apply to the actual event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compatibility and score invariance transport the checked indexed-row lower bound back to the original event."))), DescribeRole.Theorem)))));
}
