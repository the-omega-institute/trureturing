using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MacroscopicFreezingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform freezing of macroscopic lengths",
        H("Uniform freezing of macroscopic lengths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("freezing-bound"),
                DeclarationHandle.Create(Prefix + "freezing_bound"),
                H("Finite freezing error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M>=1, L>=0 and n>0. A nonnegative C1 length a on [1,2], bounded by M with derivative bounded by L, is frozen at the left endpoints of n equal blocks. Under the window variance bound and the stated scale inequalities, the sum of squared block errors divided by X*X^theta*log(X) is at most 120*(1+L)*(1/n+M*X^theta/X)+640*(1+L)*epsilon. The mean value inequality bounds each endpoint gap by L*X^theta/n, and the local endpoint estimate retains each block length X/n+M*X^theta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("freezing-eventually"),
                DeclarationHandle.Create(Prefix + "freezing_eventually"),
                H("Uniform eventual freezing error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the qualitative variance-band asymptotic, fix M>=1, L>=0 and n>0. For every eta>0, all sufficiently large X simultaneously satisfy freezingError<=120*(1+L)/n+eta for every nonnegative C1 length a bounded by M with derivative bounded by L. The threshold precedes the choice of a. The power-band conditions hold eventually, the macroscopic scale ratio tends to zero, and the window error can be chosen arbitrarily small."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-square-eventually"),
                DeclarationHandle.Create(Prefix + "normalized_square_eventually"),
                H("Uniform square bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the variance-band asymptotic, fix M>=1 and L>=0. For all sufficiently large X, every nonnegative C1 length a bounded by M with derivative bounded by L has normalized square integral at most 880*M. Apply the same endpoint comparison on the whole dyadic interval with frozen length zero, gap bound M*X^theta, and window error at most one."))),
                DescribeRole.Theorem))));
}
