using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class SourceAwareSchurDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-probe Schur response, simultaneous gauge/source descent, positive graph Gram metric, and a finite nilpotency-loss witness. Block inversion is reused from pinned Mathlib.",
        H("SourceAwareSchur"),
        Blocks(new[]
        {
                "source_preserving_schur",
                "schur_graph_lift",
                "gauge_and_source_descent",
                "graph_gram",
                "graph_gram_positive",
                "riccati_intertwines",
                "intertwined_gram_selfadjoint",
                "riccati_residual",
                "projected_nilpotency_defect",
                "projected_nilpotency_counterexample"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Reduction/SourceAwareSchur." + name),
            H(name.Replace('_', ' ')),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Exact two-probe Schur response, simultaneous gauge/source descent, positive graph Gram metric, and a finite nilpotency-loss witness. Block inversion is reused from pinned Mathlib."))),
            DescribeRole.Theorem)).ToArray())));
}
