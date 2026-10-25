using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceMobius;
internal sealed class NilpotenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nilpotence", H("Nilpotence"), Blocks(
            Paragraph(Text("This is the finite source-coordinate dependency of full corrected-field inversion. Arbitrary symmetric even integral lattices, rank zero, zero charge, empty supports and indefinite norms remain in scope. No positive energy, ground pairing or Jacobi premise is used.")),
            Describe.Lean(
                DescribeId.Create("sourcemobius-nilpotence-sectorl1-monomial-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_monomial_bound"),
                H("sectorL1_monomial_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The sharp R+1 bound uses exactly Finsupp.weight(sourceWeight D), proved by a sharp Leibniz-product induction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcemobius-nilpotence-sectorl1-degree-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_degree_bound"),
                H("sectorL1_degree_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The existing weighted total degree bounds the entire finite monomial support, including constants and zero. The proof directly reuses Mathlib's Module.End.pow_map_zero_of_le to extend the monomial annihilation bound."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcemobius-nilpotence-sugawara-pow-single"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_pow_single"),
                H("sugawara_pow_single"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The equality to existing Sugawara powers is consumed by the original-Carrier sharp bound and finite-flow expansion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcemobius-nilpotence-sugawara-one-locally-nilpotent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_one_locally_nilpotent"),
                H("sugawara_one_locally_nilpotent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finite charge support gives actual Sugawara local nilpotence without any assumption on signed charge norm. Mathlib's Module.End.pow_map_zero_of_le directly extends each finite-support annihilation bound to the common exponent."))), DescribeRole.Theorem),
            Paragraph(Text("The imported Sugawara architecture retains Kalle Kytola attribution. No literature novelty is claimed. Full all-source corrected-field adjointness, the K_L/K_R coefficient law and the complete Monster, VOA, CFT, fusion, string-theory and AdS/CFT goal remain open.")))));
}
