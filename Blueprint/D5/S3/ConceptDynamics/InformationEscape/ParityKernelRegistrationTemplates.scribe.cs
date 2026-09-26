using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ParityKernelRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dependent signatures type the coordinate-record law and the two-step transition value of parity kernels.",
        H("ParityKernelRegistrationTemplates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("subcoordinate-record-signature"),
                DeclarationHandle.Create(Module + "subcoordinateRecordSignature"),
                H("Coordinate-record signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Parameters are a dimension d, a real profile on the sign hypercube of dimension d, a "
                        + "set of coordinates and a natural horizon T. States are sequences of T + 1 sign "
                        + "vectors. The sole role is Unit with one real output; the anchor type is Empty. "
                        + "Reg/D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates uses it with the "
                        + "coordinate-record law as the actual readout. The definition is an operand for "
                        + "that source-bound registration, not a theorem or a registration proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-step-kernel-signature"),
                DeclarationHandle.Create(Module + "twoStepKernelSignature"),
                H("Two-step kernel signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Parameters are a dimension d, two real profiles on the sign hypercube and a start "
                        + "vertex. States are end vertices. The sole role is Unit with one real output; the "
                        + "anchor type is Empty. The same registration module uses it with the entry of the "
                        + "two-step kernel product as the actual readout. The definition is an operand for "
                        + "that source-bound registration, not a theorem or a registration proof."))),
                DescribeRole.Definition))));
}
