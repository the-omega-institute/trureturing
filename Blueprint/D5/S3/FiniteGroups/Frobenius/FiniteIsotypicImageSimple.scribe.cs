using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class FiniteIsotypicImageSimpleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simplicity of the actual image on an isotypic semisimple module.", H("Simplicity of the actual image on an isotypic semisimple module."),
        Blocks(
            Paragraph(Text("The matrix and double-centralizer theorems are reused from Mathlib. The constructed range identification supplies simplicity of the actual restricted group-algebra image used by the normalizer center action. The field, acting algebra and carrier universes are independent.")),
            Describe.Lean(DescribeId.Create("finiteisotypicimagesimple-issimplering-actionrange"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple.isSimpleRing_actionRange"), H("isSimpleRing actionRange"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a nonzero finite-dimensional semisimple isotypic module, its endomorphism algebra is a matrix algebra over a division ring. The same holds for the bicommutant. The finite double-centralizer surjectivity theorem identifies that bicommutant with the actual action range by an explicitly bijective ring map. Thus the image itself is simple; simplicity is not an extra assumption."))), DescribeRole.Theorem))));
}
