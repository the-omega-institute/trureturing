using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeSectorGroundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorGround", H("LatticeSectorGround"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticesectorground-canonical-ground-series"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorGround.canonical_ground_series"),
                H("canonical_ground_series"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The true ground creation series is the actual cocycle times the charge-pairing Laurent power times the creation exponential. In particular the normalized leading ground coefficient is nonzero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorground-canonical-ground-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorGround.canonical_ground_normalization"),
                H("canonical_ground_normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical_ground_normalization on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorground-canonicalio-ne-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeSectorGround.canonicalIO_ne_zero"),
                H("canonicalIO_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonicalIO_ne_zero on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
