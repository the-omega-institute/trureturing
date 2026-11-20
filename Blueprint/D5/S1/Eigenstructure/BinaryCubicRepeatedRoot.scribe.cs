using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class BinaryCubicRepeatedRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Idempotence distinguishes the two binary forms with characteristic polynomial X cubed plus X.",
        H("Binary cubic forms with a repeated root"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-cubic-repeated-root-basis"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/BinaryCubicRepeatedRoot.exists_basis"),
            H("The two forms on the primary space at one"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Let f act on a three-dimensional vector space over the binary field with characteristic polynomial X cubed plus X. There is an ordered basis b0, b1, b2. The operator fixes b0 and sends b2 to zero. It fixes b1 if f is idempotent and sends b1 to b0 plus b1 otherwise.")),
                Paragraph(Text("The eigenvalue zero is a simple root of the characteristic polynomial, so the kernel has dimension one. Cayley–Hamilton gives f cubed equal to f, making the square the projection onto the complementary two-dimensional space. There f is an involution. An involution different from the identity minus the identity is a nonzero square-zero map. A vector with nonzero image and that image supply the length-two block.")),
                Paragraph(Text("These two forms give the scalar and Jordan types in the Heawood double cover classification. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108"))),
            DescribeRole.Theorem))));
}
