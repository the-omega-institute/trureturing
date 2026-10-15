using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockIntegralOddFixedSectorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral odd-target fixed-source sector",
        H("The original integral fixed-sector action"),
        Blocks(
            Paragraph(Text("The consumer keeps the original ActualTensor carrier, Leech native L0, explicit rank-24 spectrum, both Gram inverse equations and the determinant-one endpoint. Its integral sectors are the genuine intersections of the original odd target ker(S+id) with the native eigenspaces; the completed integer direct-sum theorem supplies their supremum.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockintegraloddfixedsector-ytw-omega"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockConformalIdentificationVisible.Ytw_omega"),
                H("Original conformal supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The exact original Ytw omega identity enters through the visibility supplier and is not re-proved by the consumer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockintegraloddfixedsector-integralsectorsupremum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockIntegralOddFixedSector.integralSector_supremum"),
                H("Integral odd-target decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual integer eigenspaces below two vanish, and their supremum is exactly the odd target. Bare S-fixed weight-three-halves ground states are therefore not silently relabeled as integer sectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockintegraloddfixedsector-integralphysicalmode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockIntegralOddFixedSector.integralPhysicalMode"),
                H("Fixed-source physical mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For a theta-fixed source, the original coefficient index is -2n-2 and the target weight is k+r-n-1. The mode lands in the genuine integer odd-target sector whenever this weight is an integer sector value; odd cover coefficients vanish by the original restriction."))),
                DescribeRole.Definition))));
}
