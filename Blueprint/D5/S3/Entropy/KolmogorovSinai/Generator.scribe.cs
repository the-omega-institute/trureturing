using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.KolmogorovSinai;

internal sealed class GeneratorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/morgenstern2026ks");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator", H("Generator"), Blocks(
            Paragraph(Text("Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.")),
            Describe.Lean(DescribeId.Create("ksentropypartition-le-ksentropyseq-div"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropyPartition_le_ksEntropySeq_div"),
                H("ksEntropyPartition le ksEntropySeq div"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ksentropy-eq-ksentropypartition-of-generating"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropy_eq_ksEntropyPartition_of_generating"),
                H("ksEntropy eq ksEntropyPartition of generating"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem))));
}
