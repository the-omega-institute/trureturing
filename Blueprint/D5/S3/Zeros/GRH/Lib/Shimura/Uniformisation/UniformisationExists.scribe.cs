using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class UniformisationExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformisation Exists", H("Uniformisation Exists"),
        Blocks(
            Paragraph(Text("Smooth is geometrically reduced; an abelian scheme over an algebraically closed field is integral. Torsion section of invertible order vanishing somewhere vanishes (unramified torsion). Rigidified line bundles descend along fpqc covers; pairing identities descend along isogenies. A complex abelian variety is a complex torus: charts, compactness, uniformisation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/UniformisationExists.nonempty_uniformisation"),
                H("nonempty_uniformisation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Uniformisation: an abelian variety A over ℂ, smooth of relative dimension d and embedded in projective space by a linear system N, admits a uniformisation ℂ^d/L ≅ A(ℂ).")))))));
}
