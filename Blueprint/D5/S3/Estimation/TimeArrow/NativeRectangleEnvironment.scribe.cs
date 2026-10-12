using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeRectangleEnvironmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collapsed history, rectangle membership, and outside signal-row counts recover both numeric margins. Conditioning the complete original experiment on that environment preserves the four-cell conditional law.",
        H("Minimal native rectangle environments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-minimal-readout-eq-iff"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.NativeRectangleEnvironment.native_minimal_readout_eq_iff"),
                H("Native minimal readout eq iff"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of the minimal readout is equivalent to equality of the rectangle, outside counts, and both recovered margins."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-minimal-four-cell-law"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.NativeRectangleEnvironment.native_minimal_four_cell_law"),
                H("Native minimal four cell law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The minimal native environment has the same four-cell hypergeometric conditional law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-rectangle-readout"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.NativeGlobalRectangleEnvironment.fullRectangleReadout"),
                H("Full rectangle readout"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full readout combines the collapsed original observation with its rectangle and complete outside counts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-native-four-cell-conditional-law"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.NativeGlobalRectangleEnvironment.full_native_four_cell_conditional_law"),
                H("Full native four cell conditional law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hypergeometric law applies directly to the probability weights of complete original observations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-native-conditional-mass-eq"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.NativeGlobalRectangleEnvironment.full_native_conditional_mass_eq"),
                H("Full native conditional mass eq"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conditioning original observations on the full readout agrees with the corresponding conditional mass inside the collapsed-history fiber."))),
                DescribeRole.Theorem)
        )));
}
