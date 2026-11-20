using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class NilpotentDimensionThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square distinguishes the two nonzero nilpotent normal forms in dimension three.",
        H("Nilpotent operators in dimension three"),
        Blocks(Describe.Lean(
            DescribeId.Create("nilpotent-dimension-three-basis"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilpotentDimensionThree.exists_basis"),
            H("A basis for the two normal forms"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Let f be a nonzero endomorphism of a three-dimensional vector space over any field. If f cubed is zero, there is an ordered basis b0, b1, b2. The operator sends b0 to zero and b1 to b0. It sends b2 to zero when f squared is zero, and sends b2 to b1 when f squared is nonzero.")),
                Paragraph(Text("The Jordan chain basis expresses the ranks of powers as sums of the remaining chain lengths. If the square vanishes, the nonzero first power supplies a chain of length two. The dimension count then supplies a separate chain of length one. Otherwise the rank of the square supplies a chain of length three, whose reversed order gives the required basis.")),
                Paragraph(Text("For the traceless binary matrix classification of Heawood double covers, these are the two representatives with characteristic polynomial t cubed. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108"))),
            DescribeRole.Theorem))));
}
