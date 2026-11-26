using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Chebotarev;

internal sealed class FrobeniusFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius Filter", H("Frobenius Filter"),
        Blocks(
            Paragraph(Text("Chebotarev, existence form: Frobenius elements at degree-one primes are dense. Filter of most degree-one Frobenius elements; density and properness from Chebotarev.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Chebotarev/FrobeniusFilter.chebotarev"),
                H("chebotarev"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Chebotarev: for a non-empty open W ⊂ Γ = Gal(K̄/K) and a finite set S of primes, there is v ∉ S of prime norm with a place above it all of whose arithmetic Frobenius elements lie in W.")))))));
}
