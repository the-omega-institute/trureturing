using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOuterTaylorEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed Laurent residue evaluation and Taylor reindexing.",
        H("Outer Laurent and Taylor Evaluation"),
        Blocks(
            Paragraph(Text("Signed numerator coordinates and independent pair denominators are retained throughout. The three complete outer local-residue-to-Taylor identifications, actual interchange, Lambda zero, arbitrary-first DE-L and all-charge induction are not established by these finite algebraic identities. GroundFirst remains a separate final lifting base.")),
            Describe.Lean(
                DescribeId.Create("local-laurent-pair-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.local_laurent_pair_residue"),
                H("Signed local Laurent coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Two translated Laurent factors have arbitrary integer powers. A negative local pole index yields a finite binomial convolution; a nonnegative index has zero residue. Only the two nonzero translation constants are required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-local-monomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_local_monomial"),
                H("Three independent poles in the J/A local coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Currying the original ternary monomial at y=v retains the original signed numerator powers. The three clearing orders remain independent, including the separate spectator order K."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-monomial-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_monomial_residue"),
                H("Exact current/source local monomial residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The rational normal form is expanded in the genuine Laurent field and its coefficient at minus one is evaluated. The exponent at the local diagonal may be any integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-laurent-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_laurent_residue"),
                H("Finite Laurent numerator evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The local rational residue of every finite labelled Laurent numerator is the full finite sum of its monomial values. No homogeneity or nonnegative numerator coordinate is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-signed-outer-convolution"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_signed_outer_convolution"),
                H("Signed finite convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Integer diagonal exponents add under finite binomial convolution while an arbitrary original Taylor coefficient sequence is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-forward-outer-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_forward_outer_taylor"),
                H("Forward Taylor reindexing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Independent natural pole and inner bounds determine a finite signed convolution. Reversing the supported antidiagonal gives the original forward residue weights, including empty negative total degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-reverse-outer-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_reverse_outer_taylor"),
                H("Reverse Taylor reindexing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The reverse order retains the first Taylor coordinate and gives the corresponding signed residue weights. Total degree is unrestricted and negative degree gives an empty sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-associated-contraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_associated_contraction"),
                H("Associated-coordinate Vandermonde contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Triangular finite reindexing and Vandermonde contract the associated Taylor coefficient array with an independent signed pole."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-left-outer-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_left_outer_taylor"),
                H("Fused Taylor reindexing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The associated-coordinate cocycle contracts to the original fused Taylor weights. This algebraic identity is separate from evaluation of the complete nested actual Q products."))),
                DescribeRole.Theorem))));
}
