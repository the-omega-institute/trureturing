using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialLocalGaussianDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/ouimet2020precise");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binomial local Gaussian approximation, negligible powered tails, and lattice Gaussian sums.",
        H("Binomial Gaussian Ingredients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binomial-probability-mass"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialLocalGaussian.binomialMass"),
                H("Binomial probability mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "binomialMass(p,n,i) = choose(n,i) p^i (1-p)^(n-i). "
                    + "The probability interpretation used here requires 0<p<1 and 0<=i<=n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-relative-entropy"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialLocalGaussian.binaryKL"),
                H("Binary relative entropy expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "binaryKL(x,p) = x log(x/p) + (1-x) log((1-x)/(1-p)). "
                    + "It is the entropy expression used in the Stirling expansion; "
                    + "this definition carries no claim of mathematical novelty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("relative-gaussian-growing-window"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialLocalGaussian.local_gaussian_window"),
                H("Uniform relative approximation on a growing window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each fixed 0<p<1 and every epsilon>0, all sufficiently large "
                    + "natural n and every natural k with |k-np|<=n^(7/12) satisfy "
                    + "|binomialMass(p,n,k) sqrt(2 pi n p(1-p)) "
                    + "exp((k-np)^2/(2 n p(1-p))) - 1| < epsilon. "
                    + "This is a binomial specialization of the classical local-limit "
                    + "estimate in Theorem 2.1 and its proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-power-binomial-tail"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialLocalGaussian.binomial_power_tail"),
                H("Powered tails beat every fixed polynomial scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For fixed 0<p<1, every positive natural l and every real s, "
                    + "n^s times the sum of binomialMass(p,n,i)^l over 0<=i<=n "
                    + "with |i-np|>n^(7/12) tends to zero. The proof uses the "
                    + "binomial theorem and the frozen binary Pinsker inequality, "
                    + "including both boundary indices. This is a classical tail "
                    + "ingredient in the repository's precise finite-sum formulation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("growing-lattice-gaussian-integral"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialLocalGaussian.gaussian_window_sum_limit"),
                H("Gaussian lattice sum with a moving real center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For fixed 0<p<1 and c>0, the sum of "
                    + "exp(-c ((i-np)/sqrt(n))^2) over 0<=i<=n with "
                    + "|i-np|<=n^(7/12), divided by sqrt(n), tends to sqrt(pi/c). "
                    + "The center np need not be integral. Sum-integral comparison "
                    + "and Gaussian tails supply this auxiliary limit; it is not "
                    + "a powered-ratio maximum result."))),
                DescribeRole.Theorem))));
}
