using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class OrbitClassSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbit Class Sum", H("Orbit Class Sum"),
        Blocks(
            Paragraph(Text("Polynomial roots inverting the norm, matched pairs of test functions, splitting of cocycles. Matching of unit functions at a principal tame level. Units with invertible skew part. Class sum of orbit counts equals the mass of the stabiliser's classes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/OrbitClassSum.classSum_card_orbit"),
                H("classSum_card_orbit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let G act on X, ι embed H with image the stabiliser of e, and Δ, L be the preimages of Γ, K. If f(g) counts the y in Γe with g⁻¹y in Ke, the class sum of f for (Γ, K) equals that of 1 for (Δ, L).")))))));
}
