using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel;

internal sealed class UnipotentCoordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unipotent Coords", H("Unipotent Coords"),
        Blocks(
            Paragraph(Text("Names for the real unitary group, frames, coordinates and measures on unipotent subgroups. Lebesgue measure on complex matrices in Gauss (LDU) coordinates, with its Jacobian. Matrix coordinates for the unipotent and compact subgroups fixing the frame.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/UnipotentCoords.exists_mul_unipotentOf_dualCols_eq"),
                H("exists_mul_unipotentOf_dualCols_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If B has ϱ columns that span an isotropic space and are dual to the frame sf (h(sf_a, B_b) = δ_ab, with h(sz, B_b) = 0), then B = su(e*₁, …, e*_ϱ) for some u = unipotentOf q in 𝖴⁰.")))))));
}
