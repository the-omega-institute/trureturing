using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialPoweredRatioMaximumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/byun2026unimodality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite maximum of the actual powered-sum ratio has its exact asymptotic constant.",
        H("Maximum of the Powered Binomial Ratio"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-powered-binomial-ratio-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximumValue"),
                H("Finite maximum including both endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The maximum is taken over every natural r from zero through m "
                    + "of poweredRatio, whose denominator is the powered binomial sum. "
                    + "The definition does not select a unique maximizing index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powered-binomial-ratio-maximum-asymptotic"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic"),
                H("Exact maximum asymptotic for every positive natural power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source,
                    LibraryNoteRef.Create("D5/L/Analytic/abel2013binomial"),
                    LibraryNoteRef.Create("D5/L/Analytic/ouimet2020precise")),
                Blocks(
                    Paragraph(Text(
                        "For every fixed positive real a and positive natural l, the "
                        + "maximum divided by A_m tends to one, where "
                        + "A_m = sqrt(l)/sqrt(2 pi m) times "
                        + "sqrt(1+2a)(1+a)a^((l-2)/2)/((1+a)^l-1) times "
                        + "((1+2a)/(1+a))^((m+1/2)l). "
                        + "The real exponent (l-2)/2 includes l=1 without "
                        + "natural-number subtraction. The expression is the target "
                        + "specified in Conjecture 1.1(d) for the sequence "
                        + "(1.4) of the source.")),
                    Paragraph(Text(
                        "The proof uses a floor comparison, localization of actual "
                        + "ratio maximizers, the moving-endpoint geometric factor, "
                        + "normalization of the powered denominator along both "
                        + "sequences, and a uniform sharp binomial bound. Finite "
                        + "maximum existence is proved internally and ties are allowed. "
                        + "No exact-peak, uniqueness, or unimodality premise is used. "
                        + "The complete weighted denominator normalization is a "
                        + "classical literature result; it is not claimed as a "
                        + "new discovery. Clauses (a)-(c) of the source conjecture "
                        + "are outside this theorem. The source and eligibility "
                        + "boundaries are recorded in "
                        + "Problems/glasby-paseman-powered-ratio-maximum.md; "
                        + "no typed resolution claim is made here."))),
                DescribeRole.Theorem))));
}
