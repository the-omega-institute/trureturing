using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class SelmerRelationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selmer Relations", H("Selmer Relations"),
        Blocks(
            Paragraph(Text("Selmer conditions against trivialisations; many relations at split primes: Greenberg–Wiles lower bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerRelations.exists_split_primes_relations"),
                H("exists_split_primes_relations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Relations at split primes. For U fixing M and μ_m, without complex conjugations, there are split primes, Frobenii φ_i and elements γ_i such that each family (n_i) with ∑ n_i(x(γ_i)) = 0 on Selmer cocycles x extends to an equivariant homomorphism on U giving such relations at other split primes. A bound on trivialised cocycles bounds their number below.")))))));
}
