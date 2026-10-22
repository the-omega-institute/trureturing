using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;
internal sealed class LatticeSectorFiniteSumLawsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorFiniteSumLaws", H("LatticeSectorFiniteSumLaws"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-coefficients-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.coefficients_truncation"),
                H("coefficients_truncation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("coefficients_truncation on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-coefficients-derivatives"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.coefficients_derivatives"),
                H("coefficients_derivatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("coefficients_derivatives on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-sumleft"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.sumLeft"),
                H("sumLeft"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("sumLeft on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-sumfirst"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.sumFirst"),
                H("sumFirst"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("sumFirst on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-sumsecond"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.sumSecond"),
                H("sumSecond"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("sumSecond on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorfinitesumlaws-coefficients-jacobi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws.coefficients_jacobi"),
                H("coefficients_jacobi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("coefficients_jacobi on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
