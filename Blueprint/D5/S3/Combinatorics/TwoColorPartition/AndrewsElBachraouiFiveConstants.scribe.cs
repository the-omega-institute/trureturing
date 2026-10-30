using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiFiveConstantsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "D-prime leading constants and the Wallis gap.",
        H("D-prime leading constants and the Wallis gap"),
        Blocks(
            Node("andrews-el-bachraoui-fiveconstants-odd-prod", "Odd denominator product", "oddProd", "The real product of 2i plus one for natural i strictly below h.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fiveconstants-even-prod", "Even numerator product", "evenProd", "The real product of 2i plus two for natural i strictly below h.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fiveconstants-rational-constant", "Rational coefficient leading constant", "rationalConstant", "The product of the fractions 2i plus two over 2i plus three, for i below h minus one, divided by h factorial times oddProd h.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fiveconstants-product-constant", "Gauss upper leading constant", "productConstant", "The value pi divided by two raised to h plus one times the square of h factorial.", DescribeRole.Definition),
            Node("andrews-el-bachraoui-fiveconstants-subset-constant", "Alternating subset constant", "subset_constant", "For every finite set s, the sum over its subsets S of minus one raised to the cardinality of S divided by twice that cardinality plus one equals the product, for i below the cardinality of s, of 2i plus two over 2i plus three. Integrating the finite subset expansion of one minus x squared and using the existing sine-power integral proves the formula.", DescribeRole.Theorem),
            Node("andrews-el-bachraoui-fiveconstants-leading-gap-pos", "Strict Wallis leading gap", "leading_gap_pos", "For every natural h at least one, rationalConstant h minus productConstant h is strictly positive. The existing Wallis lower bound gives a strict inequality between the squared even-to-odd product ratio and pi times h.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
