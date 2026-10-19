using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTerminalBoundSoundnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful transport from checked terminal witnesses to original centered-score inequalities.",
        H("Terminal inequalities require the earned original contractions"),
        Blocks(
            Paragraph(Text("The theorems keep the complete original contraction receipts and actual terminal checks as explicit premises. They read exact coordinate and outcome transport from each successful terminal check, then use the previously earned original-function contraction invariance to replace its stored contraction integer by the actual contraction at that terminal event. The whole-row consumers additionally use the checked complete-event tags. EJMLocalBoundAcceptance supplies every premise from the full actual numerical receipts in the same final certificate delivery.")),
            Describe.Lean(DescribeId.Create("triangle-terminal"),
                DeclarationHandle.Create(Prefix + "triangle_terminal_sound"),
                H("One checked triangle terminal bounds its original centered score"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assuming every original triangle contraction receipt, acceptance of the selected terminal's actual transport and integer comparison bounds triangleCentered F1 at its literal complete event. The conclusion is conditional on those exact numerical premises."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-terminal"),
                DeclarationHandle.Create(Prefix + "singleton_terminal_sound"),
                H("One checked singleton terminal bounds its original centered score"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The analogous conditional transport applies to singletonCentered F2 and retains its separate factor 64. The stored singleton contraction is substituted only using the earned actual contraction equation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-all-complete"),
                DeclarationHandle.Create(Prefix + "triangle_all_terminal_bounds"),
                H("Every actual complete triangle row has its required score bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance of all actual terminal checks and all row tags, together with every exact contraction receipt, yields the score inequality for any triangle row whose original rule is complete. The checked tag equality identifies the row's original event with the literal terminal event used in the proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-all-complete"),
                DeclarationHandle.Create(Prefix + "singleton_all_terminal_bounds"),
                H("Every actual complete singleton row has its required score bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire singleton complete-row domain obtains its original centered-score bound under the same three discharged-in-the-consumer premise families. This is the exact terminal premise required by the generic full-row acceptance theorem."))),
                DescribeRole.Theorem))));
}
