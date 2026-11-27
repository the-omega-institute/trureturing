using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli;

internal sealed class ThetaTorusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Torus", H("Theta Torus"),
        Blocks(
            Paragraph(Text("Projective embeddability passes to composites and to closed subschemes of finite products. A positive Riemann form forces the signature condition on the hermitian form. Canonical theta coordinates of PEL complex tori and their Heisenberg law.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/ThetaTorus.thetaCoord_vector_ne_zero"),
                H("thetaCoord_vector_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The theta functions θ_t, t in T, have no common zero: for every z in V the vector (θ_t(z))_t is non-zero.")))))));
}
