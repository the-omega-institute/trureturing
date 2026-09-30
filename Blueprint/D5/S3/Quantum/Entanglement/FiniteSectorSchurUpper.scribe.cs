using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorSchurUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical Schur channel has diamond error bounded by the attained spectral minimum.",
        H("Schur Channel Upper Bound"),
        Blocks(
            Describe.Lean(
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-sector-simplex-variational"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.simplex_quadratic_dominates_weighted_complex_form"),
                H("Simplex variational domination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonempty finite sector type and entrywise nonnegative real matrix A, "
                        + "one simplex point r simultaneously maximizes the quadratic form "
                        + "sum A(i,j) r(i) r(j) and upper-bounds every weighted complex form "
                        + "sum sqrt(p(i)) sqrt(p(j)) A(i,j) Re(conj(x(i)) x(j)) "
                        + "for simplex p and unit-l2 x.")),
                    Paragraph(Text(
                        "The proof sets y(i)=sqrt(p(i))*norm(x(i)), uses Cauchy-Schwarz to show "
                        + "sum y <= 1, fills the deficit at one coordinate to obtain a simplex "
                        + "point w >= y, and applies Re(conj(x(i))*x(j)) <= norm(x(i))*norm(x(j)). "
                        + "This is the finite-sector variational step for passive-reference bounds; "
                        + "it does not assert a continuum gravitational RT identity."))),
                DescribeRole.Theorem))));
}
