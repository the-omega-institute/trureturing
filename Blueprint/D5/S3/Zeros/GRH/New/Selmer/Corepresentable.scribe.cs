using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class CorepresentableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corepresentable", H("Corepresentable"),
        Blocks(
            Paragraph(Text("New primes with anticyclotomic characters, auxiliary sets, families of interpolated L-values. Anticyclotomic character of order ℓ^N ramified at one new prime with prescribed Frobenius. Even classes, new places with tame generators, triangular system of primes. Balanced representations, pencils of tied primes, ties, twists at a point. Selmer groups are finitely presented: cocycles unramified off S read at finitely many points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/Corepresentable.exists_corepresenting_coords"),
                H("exists_corepresenting_coords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given m ≠ 0, a neighbourhood W of 1 and S finite, there are finitely many coordinates γ and R ⊇ mΛ^ι such that, for every Λ-module B killed by m with W acting trivially on B^n, evaluation at γ bijects selmerModule onto the w in B^ι killed by R.")))))));
}
