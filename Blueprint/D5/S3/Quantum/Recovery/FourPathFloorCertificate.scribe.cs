using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathFloorCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seven rational majorants in the Section 71 four-path estimate are uniformly below the common floor 49359/40000.",
        H("Four-path Section 71 finite floor certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-nonroot"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentNonroot"),
                H("Section 71 non-radical segment bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven entries are the non-radical upper bounds in equation (71.8) of the repository's Continuation VI theory volume."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-radical"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentRadical"),
                H("Section 71 radical segment bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven entries are the radical upper bounds in equation (71.8), recorded as exact positive rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-section-71-segment-majorants-lt-floor"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor"),
                H("Finite segment majorants below the common floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every one of the seven rows, the recorded non-radical and radical bounds sum to a value strictly below 49359/40000. The result is the finite rational arithmetic core of Section 71.")),
                    Paragraph(Text("This certificate does not define G_- or the triangular domain, prove the geometric support bounds, or establish the energy threshold bridge. Those parts of Theorem 71.1 remain open."))),
                DescribeRole.Theorem))));
}
