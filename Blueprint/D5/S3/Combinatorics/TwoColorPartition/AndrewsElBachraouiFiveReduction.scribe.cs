using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiFiveReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact D-prime source coefficient transformations.",
        H("Exact D-prime source coefficient transformations"),
        Blocks(
            Node("andrews-el-bachraoui-fivereduction-rational-trunc", "Finite rational truncation", "rationalTrunc", "For k, m and N natural, this is the finite transformed numerator sum through N, multiplied by the first k minus one odd geometric denominators.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-product-trunc", "Finite subtracted product", "productTrunc", "The product has the source factors with exponents 2 plus 2i and 2k plus 2i and two odd geometric denominator factors, for i from zero through N.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-geom-mul-one-sub", "Geometric inverse identity", "geom_mul_one_sub", "For every positive natural e, geom e times one minus X raised to e equals one. The series is the original integer coefficient definition.", DescribeRole.Theorem),
            Node("andrews-el-bachraoui-fivereduction-offset-indices", "Finite offset indices", "offsetIndices", "The disjoint sum of ranges m minus one and k minus m minus one indexes the even and odd source numerator offsets. Empty endpoint ranges are retained.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-offset", "Source numerator offsets", "offset", "An even index i has offset 2 plus 2i. An odd index i has offset 2m plus one plus 2i.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-rational-series", "Fixed rational series", "rationalSeries", "The sum over subsets of the offset indices has sign minus one raised to the subset cardinality, monomial degree equal to the sum of its offsets, and geometric step twice its cardinality plus one. The sum is multiplied by the odd geometric denominator product.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-source-coefficient-reduction", "Exact transformed source coefficient", "source_coefficient_reduction", "For every k, m and n with one at most m and m less than k, the original dCoeff k m n equals the coefficient of degree n of rationalTrunc k m n minus productTrunc k n. There is no degree shift. Two applications of the existing nilpotent q-binomial identity prove the transformation in the quotient by X raised to n plus one.", DescribeRole.Theorem),
            Node("andrews-el-bachraoui-fivereduction-gauss-series", "Consistent Gauss coefficients", "gaussSeries", "This fixed integer power series has coefficient at n equal to the source productTrunc 2 n coefficient. Truncation stability connects its lower coefficients to each finite product.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-product-series", "Finite even convolution product", "productSeries", "For k at least two this is gaussSeries multiplied by geom 4 through geom of twice k minus two.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fivereduction-source-coefficient-expansion", "Fixed-series source coefficient identity", "source_coefficient_expansion", "For every k, m and n with one at most m and m less than k, dCoeff k m n is the degree n coefficient of rationalSeries k m minus that of productSeries k. Finite subset expansion, geometric summation and product cancellation prove every coefficient bridge.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
