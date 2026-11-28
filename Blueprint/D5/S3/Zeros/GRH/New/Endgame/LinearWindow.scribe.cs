using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class LinearWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear Polar Window", H("Linear Polar Window"),
        Blocks(
            Paragraph(Text("Factorial Laplace moments control a second scale in a fixed linear window.")),
            Describe.Lean(DescribeId.Create("linear-polar-window"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/LinearWindow.exists_linear_window_sub_mul_le"),
                H("A good scale in a linear window"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two polar real error functions E and E', there is a real constant C greater than one such that, for every sufficiently large real t and every coefficient X between zero and exp(t), some u between t and C times t satisfies E(u) minus X times E'(u) at most exp(-t). The constant depends on the two functions, and the threshold for t is uniform in X. The proof chooses a common moment radius R between three and four and the moment order ceil(C times t divided by nine), with C = 99/(log(R)-log(3)). Two exponential majorants control the tails outside the window; their integrals and the signed moment error are together smaller than the negative constant contribution.")))))));
}
