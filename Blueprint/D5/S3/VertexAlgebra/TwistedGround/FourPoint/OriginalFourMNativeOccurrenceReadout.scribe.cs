using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMNativeOccurrenceReadoutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native occupations of a labelled affine word",
        H("Four independent factorial weights"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-m-native-slot-occupation"),
                DeclarationHandle.Create(Prefix + "slotOccupation"),
                H("Occupation of one native slot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count the letters of a list of oscillators in the finite support "
                    + "and extend the occupation by zero along the support embedding."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("four-m-native-occurrence-readout"),
                DeclarationHandle.Create(Prefix + "native_occurrence_readout"),
                H("Affine moment in four occupations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let the occurrence labels form a finite type and map them "
                    + "into the two compact external legs, each with an input and an output slot. "
                    + "Given a symmetric complex matrix on the tagged support and a complex mean "
                    + "on it, evaluate the affine moment at the word's occupation using the "
                    + "pulled-back matrix and mean. It equals the affine coefficient of the original "
                    + "matrix and mean at the joined external occupation, multiplied by the four "
                    + "factorial weights. Compute each occupation by filtering the mapped word "
                    + "first by leg and then by slot. Repeated labels and coincident images count "
                    + "with their full multiplicities."))),
                DescribeRole.Theorem))));
}
