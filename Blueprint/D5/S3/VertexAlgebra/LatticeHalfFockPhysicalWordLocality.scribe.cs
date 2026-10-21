using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalWordLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical charged words are local at one order uniformly over every pair of signed physical slice shifts.",
        H("Uniform Physical Word Locality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalwordlocality-uniform-word"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality.physicalWord_locality"),
                H("Uniform signed-shift word locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The order is built before both signed shifts by the ordinary Dong induction, using canonical cons shifts and no recursive auxiliary word field."))),
                DescribeRole.Theorem))));
}
