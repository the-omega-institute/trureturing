using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeSectorIntertwinerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorIntertwiner", H("LatticeSectorIntertwiner"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-sector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.Sector"),
                H("Sector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Sector on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-inclusion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.inclusion"),
                H("inclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("inclusion on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-projection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.projection"),
                H("projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("projection on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-charge-homogeneity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.charge_homogeneity"),
                H("charge_homogeneity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every actual ordinary field mode on arbitrary original oscillator inputs has output charge equal to the sum of its two input charges. Both normal-product branches and the polynomial linear extension are covered."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-canonical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.canonical"),
                H("canonical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorintertwiner-inclusion-canonical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorIntertwiner.inclusion_canonical"),
                H("inclusion_canonical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("inclusion_canonical on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
