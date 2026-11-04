using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Rectangular;
internal sealed class FiniteSectorRectangularAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attaining orthonormal pairs for finite rectangular Ky Fan sums.", H("Rectangular attainment"),
        Blocks(Describe.Lean(DescribeId.Create("rectangular-attainment"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Rectangular/FiniteSectorRectangularAttainment.exists_orthonormal_re_sum_inner_map_eq_ky_fan_sum"),
            H("Attaining orthonormal pair"),StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
            Blocks(Paragraph(Text("For a real or complex finite-dimensional linear map between possibly unequal dimensions, every natural k at most both dimensions admits orthonormal source and target k-families attaining the real paired trace. The original Gram eigenbasis provides the source family; normalization on the positive singular directions and orthonormal extension provide the target family. The empty family remains legal. This is the original attainment argument used by sector_pair, with no additional completeness or nontriviality assumptions."))),DescribeRole.Theorem))));
}
