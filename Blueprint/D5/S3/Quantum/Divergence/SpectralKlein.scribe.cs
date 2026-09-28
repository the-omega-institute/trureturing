using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SpectralKleinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spectral-overlap proof of the actual matrix Klein inequality, with a possibly singular first matrix and a positive definite reference.",
        H("Noncommuting Matrix Klein Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-overlap-row-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SpectralKlein.overlap_row_sum"),
                H("Row normalization comes from the actual unitary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weights are squared moduli of entries of an actual complex unitary matrix. Its product with its adjoint yields every row sum."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-overlap-column-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SpectralKlein.overlap_col_sum"),
                H("Column normalization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reverse unitary identity supplies the second normalization needed to account for the reference trace."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommuting-spectral-cross-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SpectralKlein.trace_spectral_mul"),
                H("Cross trace for independently diagonalized matrices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eigenbases may differ. Cyclicity of trace reduces the matrix expression to their actual overlap weights; simultaneous diagonalization is not assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-klein-faithful-reference"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SpectralKlein.klein_trace_nonneg"),
                H("Klein inequality including singular first matrices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix spectral theorem and scalar log tangent bound give nonnegativity of Re Tr(A(log A-log B)-A+B). A is positive semidefinite and B is positive definite. Matrix CFC logarithms are used explicitly."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faithful-quantum-relative-entropy-nonnegative"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SpectralKlein.faithful_relative_entropy_nonneg"),
                H("Nonnegative relative entropy of normalized matrices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Trace-one normalization cancels the affine Klein terms. This establishes the faithful-reference mathematical statement in proof-source form; quantum measurement DPI and Pinsker are separate obligations. No kernel verification is asserted by this explanatory Scribe."))), DescribeRole.Theorem))));
}
