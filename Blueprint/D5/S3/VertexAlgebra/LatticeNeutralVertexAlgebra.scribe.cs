using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeNeutralVertexAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeNeutralVertexAlgebra", H("LatticeNeutralVertexAlgebra"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticeneutralvertexalgebra-neutraly"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeNeutralVertexAlgebra.neutralY"),
                H("neutralY"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("neutralY on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeneutralvertexalgebra-neutraly-modes"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeNeutralVertexAlgebra.neutralY_modes"),
                H("neutralY_modes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("neutralY_modes on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeneutralvertexalgebra-action-vacuum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeNeutralVertexAlgebra.action_vacuum"),
                H("action_vacuum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("action_vacuum on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeneutralvertexalgebra-neutralvertexalgebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeNeutralVertexAlgebra.neutralVertexAlgebra"),
                H("neutralVertexAlgebra"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("neutralVertexAlgebra on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
