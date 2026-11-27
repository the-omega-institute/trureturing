using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class BaseChangePlacesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Change Places", H("Base Change Places"),
        Blocks(
            Paragraph(Text("A totally complex number field with a conjugation for all embeddings is CM. E[X]/P is CM when roots have constant modulus; its finite adeles as polynomials. Cyclic prime-degree CM extension with test character; compatible CM types; matched places. Base change map and Galois action on finite adelic points of unitary groups. Places above a set, adelic matched pairs, basic compatibilities of base change maps.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangePlaces.adjoinRoot_cm_presentation"),
                H("adjoinRoot_cm_presentation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P be monic irreducible over the CM field E, all complex roots satisfying r r̄ = ν ∈ ℚ. Then L = E[X]/(P) is CM, θθ̄ = ν, and X ↦ θ presents 𝔸_{L,f} as 𝔸_{E,f}[X]/(P), compatibly with L and conjugation.")))))));
}
