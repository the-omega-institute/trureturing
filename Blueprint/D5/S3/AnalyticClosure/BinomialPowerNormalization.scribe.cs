using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialPowerNormalizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/abel2013binomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete sum of every positive integer power of binomial masses has its classical normalization.",
        H("Complete Binomial Power Normalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-binomial-power-normalization"),
            DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialPowerNormalization.binomial_power_normalization"),
            H("Exact Gaussian normalization for all positive natural powers"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "For each fixed 0<p<1 and positive natural l, the complete sum "
                    + "of binomialMass(p,n,i)^l over 0<=i<=n, divided by "
                    + "(2 pi n p(1-p))^((1-l)/2)/sqrt(l), tends to one. "
                    + "The exponent uses real subtraction, including l=1.")),
                Paragraph(Text(
                    "For l>=2 this is the classical weighted complete-sum estimate "
                    + "of Theorem 3.1 under r=l-1 and z=a^l, with p=a/(1+a). "
                    + "The case l=1 is exact by the binomial theorem. The local "
                    + "Gaussian source also gives the l=2,3 cases in equations "
                    + "(3.12)-(3.13): "), Ref("D5/L/Analytic/ouimet2020precise"),
                    Text(". These denominator estimates do not settle the maximum "
                    + "of the truncated ratio."))),
            DescribeRole.Theorem))));
}
