using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PathCurrentRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dependent signature types one real statistic of a whole path in a signed state space with a peak.",
        H("PathCurrentRegistrationTemplates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-peak-path-signature"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates.signedPeakPathSignature"),
                H("Signed-peak path signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Parameters are an arbitrary state type X, a real sign function on X, a peak state, "
                        + "two real profile values, a real normalizer and a natural horizon. States are "
                        + "whole paths N -> X. The sole role is Unit, and its output is one real number; "
                        + "the anchor type is Empty. Reg/D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent "
                        + "uses this signature with the forward-versus-reversed log-likelihood of the "
                        + "single-peak parity kernel as the actual readout. The definition is an operand "
                        + "for that source-bound registration, not a theorem or a registration proof."))),
                DescribeRole.Definition))));
}
