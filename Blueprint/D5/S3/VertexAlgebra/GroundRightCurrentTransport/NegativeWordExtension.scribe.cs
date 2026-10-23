using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class NegativeWordExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative-current first-source extension", H("NegativeWordExtension"), Blocks(
            Describe.Lean(DescribeId.Create("projected-ground-left-current-word"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/GroundRightCurrentTransport/NegativeWordExtension.projectedGround_left_current_word"),
                H("projectedGround_left_current_word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("From the exact charged ground-pair family and the compiled conditional left_current_step, induction over every finite negative-current word transports compatibility to the first source. Each letter contributes one signed lift, while the word and ground signs remain explicit.")),
                    Paragraph(Text("The remaining audit gap is the lawful source-selection, whole-family variation, sensitivity and observational-dependence evidence required for four-slot registration; this is disclosed under the existing concrete issue #20510."))), DescribeRole.Theorem))));
}
