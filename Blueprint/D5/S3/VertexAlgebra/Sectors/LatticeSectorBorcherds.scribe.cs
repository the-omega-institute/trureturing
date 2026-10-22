using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;
internal sealed class LatticeSectorBorcherdsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorBorcherds", H("LatticeSectorBorcherds"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.action"),
                H("action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("action on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-sectort"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.sectorT"),
                H("sectorT"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("sectorT on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-single-canonical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.single_canonical"),
                H("single_canonical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("single_canonical on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-single-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.single_action"),
                H("single_action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("single_action on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-single-sectort"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.single_sectorT"),
                H("single_sectorT"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("single_sectorT on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-canonical-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.canonical_truncation"),
                H("canonical_truncation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical_truncation on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-canonical-source-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.canonical_source_derivative"),
                H("canonical_source_derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical_source_derivative on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-canonical-target-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.canonical_target_derivative"),
                H("canonical_target_derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical_target_derivative on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-mixedleft"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.mixedLeft"),
                H("mixedLeft"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("mixedLeft on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-mixedfirst"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.mixedFirst"),
                H("mixedFirst"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("mixedFirst on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-mixedsecond"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.mixedSecond"),
                H("mixedSecond"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("mixedSecond on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorborcherds-canonical-borcherds"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds.canonical_borcherds"),
                H("canonical_borcherds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("canonical_borcherds on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
