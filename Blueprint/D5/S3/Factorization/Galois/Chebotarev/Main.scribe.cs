using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class MainDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebotarev Density Theorem.",
        H("Chebotarev Density Theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chebotarev-density"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Main.chebotarev_density"),
                H("Chebotarev Density Theorem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite Galois extension L/K of number fields and any conjugacy class C in " +
                    "Gal(L/K), the unramified prime ideals of K whose Frobenius class is C have Dirichlet " +
                    "density |C| / |Gal(L/K)|."))),
                DescribeRole.Theorem)
        )));
}
