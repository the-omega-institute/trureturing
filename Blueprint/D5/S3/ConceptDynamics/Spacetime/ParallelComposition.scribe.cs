using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ParallelCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parallel Archive Composition.",
        H("Parallel Archive Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parallelcomposition-parallel"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ParallelComposition.parallel"),
                H("Complete tagged archive composition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both complete archives are copied using literal tags zero and one. All four attributes "
                    + "and only the internal causal relations are copied. Current regions and selections use "
                    + "the same tagged disjoint union."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parallelcomposition-q-parallel"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ParallelComposition.q_parallel"),
                H("Parallel readout is additive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual selected signed sum separates over the two disjoint components. The "
                    + "background theorem uses the entire current regions, and balanced inputs remain balanced. "
                    + "All statements include empty archives and empty selections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parallelcomposition-embeddingleft"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ParallelComposition.embeddingLeft"),
                H("Old archives and their tags are retained"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both input archives have attribute-preserving order embeddings. Event membership "
                    + "recovers each tagged component, and archive cardinality is the sum of the input "
                    + "cardinalities. These equalities retain the data required for later raw cancellation."))),
                DescribeRole.Definition))));
}
