using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class TypeFrobeniusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type Frobenius", H("Type Frobenius"),
        Blocks(
            Paragraph(Text("With one ramified character, U equals Frobenius where tame inertia acts non-trivially.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/TypeFrobenius.hecke_eq_frob_on_parahoricEigenspace"),
                H("hecke_eq_frob_on_parahoricEigenspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let y in x be pro-p-Iwahori fixed at w ∤ ℓ, the line stabiliser acting by χ of the top left entry, χ(u) ≠ 0, χ(u)^(n!) ≠ 1. Then tr((τ − 1)M)·G(U)y = tr(G(s)(τ − 1)M)·y via ι, in the Galois representation of x, for G in ℂ[X], any matrix M, U the Hecke operator of diag(ϖ,1,…,1).")))))));
}
