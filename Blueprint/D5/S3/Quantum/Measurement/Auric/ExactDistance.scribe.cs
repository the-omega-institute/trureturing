using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ExactDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matching lower and upper bounds for finite mixtures",
        H("Matching lower and upper bounds for finite mixtures"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-finite-protocol-distance"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ExactDistance.exact_finite_protocol_distance"),
            H("Matching lower and upper bounds for finite mixtures"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The fixed two-flag witness gives a uniform lower bound. The explicit finite random draw of 4096 projective trees attains the upper bound over all finite reference systems."))),
            DescribeRole.Theorem))));
}
