using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class HomogeneousCoordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous Coords", H("Homogeneous Coords"),
        Blocks(
            Paragraph(Text("Homogeneous Noether normalisation and Galois closure of the cone over a variety. Homogeneous coordinates of points under a projective embedding; global functions constant on components.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/HomogeneousCoords.exists_galois_closure"),
                H("exists_galois_closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Galois closure: a Noether normalisation Λ of g yields a finite group G, finite injective f: k[X] → B and solutions b_σ of the homogeneous equations of g with Λ(b_σ) = f(X), such that geometric points φ, ψ with ψf(X) = uφf(X) have ψ(b_σ) = uφ(b_{τσ}) for some τ.")))))));
}
