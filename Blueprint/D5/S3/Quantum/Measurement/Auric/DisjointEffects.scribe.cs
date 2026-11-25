using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class DisjointEffectsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp disjoint-support spectral budget",
        H("The sharp disjoint-support spectral budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-greatest-disjoint"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DisjointEffects.isGreatest_disjoint"),
                H("The same binary maximum for both spectral objectives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/massey2010noncommutativeschurhorn")),
                Blocks(
                    Paragraph(Text("For distinct labels i, k, a, assume capacity m_a covers the working dimension and m_i + m_k is at most that dimension. The trace data lie between zero and their capacities and sum to the dimension. Both objectives attain m_i h₂(t_i/m_i) + m_k h₂(t_k/m_k). Flat factors and diagonal Jensen bound every tuple. Two disjoint coordinate subspaces give a common attaining tuple. A zero-capacity term is zero."))),
                DescribeRole.Theorem))));
}
