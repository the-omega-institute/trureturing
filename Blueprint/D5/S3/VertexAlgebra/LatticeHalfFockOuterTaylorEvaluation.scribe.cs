using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOuterTaylorEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Current and first-source Laurent residue",
        H("LatticeHalfFockOuterTaylorEvaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-laurent-pair-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.local_laurent_pair_residue"),
                H("local_laurent_pair_residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-local-monomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_local_monomial"),
                H("current_source_local_monomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-monomial-value"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.currentSourceMonomialValue"),
                H("currentSourceMonomialValue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("current-source-monomial-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_monomial_residue"),
                H("current_source_monomial_residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("current-source-laurent-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_laurent_residue"),
                H("current_source_laurent_residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-associated-contraction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_associated_contraction"),
                H("finite_associated_contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-left-outer-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_left_outer_taylor"),
                H("finite_left_outer_taylor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The current/source diagonal is taken before either remaining order. The signed monomial residue and the finite associated-coordinate contraction feed the exact fused FIRST proof. Negative degrees, empty supports and independent bounds remain included."))),
                DescribeRole.Theorem))));
}
