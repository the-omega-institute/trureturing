using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.KolmogorovSinai;

internal sealed class GeneratorConditioningDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/morgenstern2026ks");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GeneratorConditioning", H("Generator Conditioning"), Blocks(
            Paragraph(Text("Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.")),
            Describe.Lean(DescribeId.Create("generatedsigmaalgebra-le"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_le"),
                H("generatedSigmaAlgebra le"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("abramovrokhlin-partition-of-defect"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.abramovRokhlin_partition_of_defect"),
                H("abramovRokhlin partition of defect"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("condentropy-ksjoin-le-nsmul-log-card"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_ksJoin_le_nsmul_log_card"),
                H("condEntropy ksJoin le nsmul log card"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("condentropy-tendsto-isup"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_tendsto_iSup"),
                H("condEntropy tendsto iSup"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generatedsigmaalgebra-ksjoin-mono"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_ksJoin_mono"),
                H("generatedSigmaAlgebra ksJoin mono"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("comap-iterate-generatedsigmaalgebra-ksjoin-le"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.comap_iterate_generatedSigmaAlgebra_ksJoin_le"),
                H("comap iterate generatedSigmaAlgebra ksJoin le"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("isup-generatedsigmaalgebra-ksjoin-eq"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.iSup_generatedSigmaAlgebra_ksJoin_eq"),
                H("iSup generatedSigmaAlgebra ksJoin eq"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(), DescribeRole.Theorem))));
}
