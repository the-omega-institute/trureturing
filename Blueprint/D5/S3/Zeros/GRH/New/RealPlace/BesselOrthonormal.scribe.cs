using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class BesselOrthonormalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Orthonormal", H("Bessel Orthonormal"),
        Blocks(
            Paragraph(Text("the coordinates of the full function of a Bessel system are orthonormal.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/BesselOrthonormal.orthonormal"),
                H("orthonormal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The coordinates W_i of the full function of a Bessel system are orthonormal in L²(𝖴∖G₁): the integral of W_i times the conjugate of W_j is δ_ij.")))))));
}
