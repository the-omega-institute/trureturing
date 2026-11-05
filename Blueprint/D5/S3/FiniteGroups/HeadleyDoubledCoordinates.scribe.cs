using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyDoubledCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The doubled-coordinate subgroup and E4 quotient", H("The doubled-coordinate subgroup and E4 quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-doubledcoordinates-quotienthom"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom"),
                H("Reduction of exactly two coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homomorphism reduces the two selected positive coordinates modulo two and ignores all remaining coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-doubledcoordinates-quotienthom-surjective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom_surjective"),
                H("Every E4 coset occurs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two canonical cyclic reductions are surjective. The remaining coordinates can be set to zero, so the paired reduction is onto E4."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headley-doubledcoordinates-kernelequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernelEquiv"),
                H("The subgroup has the lowered coordinate type"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lowered coordinate product embeds into the original group through the two cyclic kernel inclusions, with every other factor retained. Its image is the doubled-coordinate range. The proved equality of that range with the literal reduction kernel supplies the codomain of the embedding equivalence used to transport the recursive R-cycle."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-doubledcoordinates-quotientequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientEquiv"),
                H("The actual quotient is E4"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first isomorphism theorem identifies the quotient by this literal kernel with ZMod 2 times ZMod 2. No additive splitting of the extension is assumed."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-doubledcoordinates-kernel-eq-doubled-range"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernel_eq_doubled_range"),
                H("The kernel is the doubled-coordinate range"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugating doubling on the two selected coordinates by the coordinate chart gives an endomorphism of the original product. Its range is exactly the selected kernel. This equality identifies the actual image of the lowered-coordinate embedding with the subgroup used by the nonsplit extension construction."))), DescribeRole.Theorem))));
}
