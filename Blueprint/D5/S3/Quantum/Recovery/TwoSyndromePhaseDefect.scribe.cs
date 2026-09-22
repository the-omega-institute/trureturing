using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class TwoSyndromePhaseDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The formal declarations give exact complex phase identities. They do not assert diamond-norm optimal recovery or a geometric holonomy theorem.",
        H("TwoSyndromePhaseDefect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-phase-defect"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect.weighted_phase_defect"),
                H("weighted phase defect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formal declarations give exact complex phase identities. They do not assert diamond-norm optimal recovery or a geometric holonomy theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-visibility-iff-phases-equal"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect.unit_visibility_iff_phases_equal"),
                H("unit visibility iff phases equal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formal declarations give exact complex phase identities. They do not assert diamond-norm optimal recovery or a geometric holonomy theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("opposite-phase-erasure"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect.opposite_phase_erasure"),
                H("opposite phase erasure"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formal declarations give exact complex phase identities. They do not assert diamond-norm optimal recovery or a geometric holonomy theorem."))),
                DescribeRole.Theorem))));
}
