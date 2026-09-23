using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialMaximumLocalizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/byun2026unimodality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor comparison and exponential separation for a prefix with the simplified exponential denominator.",
        H("Localization for the Simplified Binomial Prefix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplified-binomial-prefix"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialMaximumLocalization.prefixValue"),
                H("Prefix with denominator (1+a)^(rl)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "prefixValue(a,l,m,r) is the sum of (choose(m,i) a^i)^l "
                    + "over 0<=i<=r, divided by (1+a)^(rl). For l>1 this "
                    + "denominator is not the sum of the powered row-r terms "
                    + "in the published ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("simplified-prefix-floor-comparison"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialMaximumLocalization.floor_comparison"),
                H("Floor comparison with a positive limiting constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For fixed a>0 and positive natural l, put q=a/(1+2a) "
                    + "and B=(1+2a)/(1+a). Then "
                    + "prefixValue(a,l,m,floor(mq)) B^(-ml) "
                    + "sqrt(2 pi m q(1-q))^l tends to "
                    + "1/(1-(1+a)^(-l)). The floor is the natural floor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simplified-prefix-exponential-separation"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialMaximumLocalization.separated_prefix_bound"),
                H("Uniform separation away from the limiting slope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a>0, every natural l (including zero), epsilon>0, "
                    + "m>0 and 0<=r<=m with |r/m-a/(1+2a)|>=epsilon, "
                    + "prefixValue(a,l,m,r)/B^(ml) is at most "
                    + "(m+1) exp(-l m min(epsilon^2/2, epsilon log(1+a)/2)), "
                    + "where B=(1+2a)/(1+a). Both boundary indices are covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simplified-prefix-maximizer-slope-endpoint"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialMaximumLocalization.maximizer_slope_and_endpoint"),
                H("Slope and endpoint factor for every maximizing choice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For fixed a>0 and positive natural l, any r(m)<=m "
                    + "maximizing prefixValue over every 0<=j<=m satisfies "
                    + "r(m)/m -> a/(1+2a). Along that same sequence, the "
                    + "truncated numerator divided by its powered endpoint "
                    + "term tends to 1/(1-(1+a)^(-l)). Ties are allowed. "
                    + "This concerns the simplified prefix only and supplies "
                    + "neither an exact maximizing index nor the Gaussian "
                    + "prefactor for the actual powered-ratio maximum."))),
                DescribeRole.Theorem))));
}
