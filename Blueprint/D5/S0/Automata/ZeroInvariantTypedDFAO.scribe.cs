using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class ZeroInvariantTypedDFAODocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anchored zero-invariant typed DFAOs internalize the leading-zero and zero-output conventions used by published sparse-automata experiments.",
        H("Anchored Zero-Invariant Typed DFAOs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-prefix-observational-invariance"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/ZeroInvariantTypedDFAO.AnchoredZeroInvariantTypedDFAO.evalOutput_replicate_zero"),
                H("Finite leading-zero prefixes are observationally invisible"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The start-state zero loop is stored as machine evidence. Iterating that loop leaves the reached state unchanged, so any finite zero prefix preserves the output on the remaining word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-word-anchor-output"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/ZeroInvariantTypedDFAO.AnchoredZeroInvariantTypedDFAO.evalOutput_singleton_zero"),
                H("The zero word reads the distinguished anchor output"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The stored start-state output and zero-loop evidence make the published zero anchor a theorem of the machine structure rather than an external solver convention."))),
                DescribeRole.Theorem)),
        []));
}
