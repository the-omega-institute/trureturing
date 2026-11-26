using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class SphericalAllRanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spherical All Ranks", H("Spherical All Ranks"),
        Blocks(
            Paragraph(Text("Galois representations for eigenforms of any rank, compatible at spherical places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SphericalAllRanks.sphericalCompat_std"),
                H("sphericalCompat_std"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E with Weil data, every eigenform f on the definite U(n) has an attached ℓ-adic representation. If K_w fixes f, each attached one is unramified or crystalline at w, with the jumps of f's weight, and any Hecke polynomial there kills geometric Frobenius.")))))));
}
