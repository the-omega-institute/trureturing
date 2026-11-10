using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenSectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-Pole Strip Kernel Comparison",
        H("Six-Pole Strip Kernel Comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteensector"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenSector.h14_kernel_bounds"),
            H("Six-Pole Strip Kernel Comparison"), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every complex rho in the open strip with imaginary square above 100, the six-pole reciprocal kernel is positive. If the imaginary square is at most 196, twice its weight is at least 345650537/72636763553532703907200. The generic polar-angle and derivative proofs compare u and p on the closed auxiliary strip. The actual strip and height-ten premises are paid by the original exhaustive zero family at the final application; both signs and all multiplicities remain present."))),
            DescribeRole.Theorem))));
}
