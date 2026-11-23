using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondExponentialSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/ExponentialSeries.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The labeled exponential formula and the Mobius inverse.",
        H("The labeled exponential formula and the Mobius inverse"),
        Blocks(
            Node("RootBlock",
                "The subsets of the labeling set containing a specified root.", DescribeRole.Definition),
            Node("labeledWeight",
                "Sum the product of block weights by size over the partitions with exactly k blocks.", DescribeRole.Definition),
            Node("labeledWeight_root",
                "When the root lies in the labeling set, obtain the weight for k plus one blocks by choosing its root block and partitioning the complement into k blocks.", DescribeRole.Theorem),
            Node("blockSeries",
                "The formal series with zero constant coefficient and degree-m coefficient given by w(m) divided by m factorial for positive m.", DescribeRole.Definition),
            Node("scale",
                "The image of n factorial divided by k factorial in the rational algebra.", DescribeRole.Definition),
            Node("labeledWeight_coeff",
                "The weight of partitions of S into k blocks is the degree-card(S) coefficient of the k-th power of the block series, multiplied by card(S) factorial over k factorial.", DescribeRole.Theorem),
            Node("assemblyKernel",
                "The formal series with degree-k coefficient f(k) divided by k factorial.", DescribeRole.Definition),
            Node("coeff_subst_blockSeries",
                "In degree n, substitution of the block series into H is the finite coefficient sum over powers from zero through n.", DescribeRole.Theorem),
            Node("labeled_subst",
                "Substituting the block series into the assembly series and multiplying the degree-card(S) coefficient by card(S) factorial gives the sum of products with f applied to the block count.", DescribeRole.Theorem),
            Node("assemblyKernel_one",
                "Constant block-count weight one gives the formal exponential.", DescribeRole.Theorem),
            Node("oneBlockEGF",
                "The exponential generating function of the one-block sums of incidence Möbius values.", DescribeRole.Definition),
            Node("inverseCoefficient",
                "The degree-k inverse-series numerator is the binomial coefficient choosing k minus one from k plus r minus two.", DescribeRole.Definition),
            Node("inverseEGF",
                "The exponential generating function of the one-block extension coefficients, with zero constant term.", DescribeRole.Definition),
            Node("inverseEGF_subst_oneBlockEGF",
                "For positive r, substituting the one-block Möbius series into the extension-count series gives X.", DescribeRole.Theorem),
            Node("oneBlockEGF_subst_inverseEGF",
                "For positive r, the composition in the opposite order also gives X.", DescribeRole.Theorem),
            Node("markedBlockEGF",
                "The one-block exponential generating function with a size-m block marked by X to the power m minus one in the polynomial coefficient ring.", DescribeRole.Definition),
            Node("psiComplete_exponential",
                "For every n and r, the rank polynomial is n factorial times the degree-n coefficient of the exponential composed with the marked block series.", DescribeRole.Theorem),
            Node("inverseFactor",
                "The finite series whose coefficient in degree i at most q is the binomial coefficient choosing i from q divided by (i+1) factorial, and zero beyond q.", DescribeRole.Definition),
            Node("inverseEGF_factor",
                "For r equal to q plus two, the inverse series is the product of the formal variable, its exponential, and the finite factor indexed by q.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
