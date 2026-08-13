using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class CompletionEmbeddingDenseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical map from a metric space into its completion has dense range.",
        H("Density of the Canonical Completion Map"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-completion-map-has-dense-range"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/CompletionEmbeddingDense.completion_embedding_dense"),
                H("The canonical completion map has dense range"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("N"), Sp, OpenBracket,
                    Operatorname, Grp(F.Id("MetricSpace")), Open, F.Id("N"), Close,
                    CloseBracket, Comma, RowBreak,
                    Operatorname, Grp(F.Id("DenseRange")), Open,
                    F.Id("coe"), Underscore, Grp(F.Id("N")), Colon, Sp,
                    F.Id("N"), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every metric space N, its canonical coercion into the uniform-space "
                        + "completion has dense range. The source assumptions of countability, "
                        + "absence of isolated points, incompleteness, and a measure are not needed "
                        + "for this density clause.")),
                    Paragraph(Text(
                        "Pinned Mathlib was queried for denseRange_coe, DenseRange Completion, "
                        + "completion dense, canonical embedding, and Completion coe. It supplies "
                        + "the exact density result as UniformSpace.Completion.denseRange_coe. The "
                        + "Lean declaration is therefore a thin wrapper with no replacement proof.")),
                    Paragraph(Text(
                        "This document partially closes clause (i) only. Clause (ii), asserting no "
                        + "isolated points together with meagerness of the image and comeagerness of "
                        + "its complement, remains unresolved. Clause (iii), asserting full measure "
                        + "of the complement for an atomless Borel probability measure, also remains "
                        + "unresolved."))),
                DescribeRole.Theorem)),
        []));
}
