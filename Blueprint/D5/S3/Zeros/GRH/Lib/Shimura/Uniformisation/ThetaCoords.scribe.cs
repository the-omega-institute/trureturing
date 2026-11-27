using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class ThetaCoordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Coords", H("Theta Coords"),
        Blocks(
            Paragraph(Text("Rigid objects: theta coordinates span sections; theta law over local rings. Multiplication by nonzero a is an isogeny; counting torsion points over C. Line bundles with theta coordinates: pull-back, product, translation, uniqueness in Appell-Humbert.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ThetaCoords.riemannForm_eq_of_isFrame"),
                H("riemannForm_eq_of_isFrame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let N, M have theta coordinates θ, θ' of types (B, χ), (B', χ') for a full lattice L along a holomorphic L-periodic e, and w trivialise N ⊗ M⁻¹. Then Riemann forms agree, χ = χ' on L, and w_{ia}(e z) = c·exp((B(z,z) − B'(z,z))/2)·θ'_a(z)/θ_i(z) where both are non-zero, c constant.")))))));
}
