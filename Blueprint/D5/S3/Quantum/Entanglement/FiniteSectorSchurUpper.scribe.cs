using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorSchurUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical Schur channel has diamond error bounded by the attained spectral minimum.",
        H("Schur Channel Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-sector-schur-upper"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.schur_upper"),
            H("Diamond upper bound from residual spectra"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The residual-overlap kernel is positive semidefinite, has diagonal one, "
                    + "and has entries at most one. A probability weight attains its minimum "
                    + "quadratic form on the nonempty finite sector simplex.")),
                Paragraph(Text(
                    "For every actual channel whose action on all logical matrices is the "
                    + "target encoding after Schur multiplication by this kernel, the unhalved "
                    + "diamond distance to the target encoding is at most twice one minus "
                    + "the spectral minimum. A pure correlated reference reduces the trace "
                    + "difference to a rank-one positive matrix minus a positive matrix of "
                    + "equal trace. Its positive spectral part has rank at most one. The "
                    + "existing finite diamond-distance theorem supplies the pure-reference "
                    + "reduction for arbitrary joint density inputs."))),
            DescribeRole.Theorem))));
}
