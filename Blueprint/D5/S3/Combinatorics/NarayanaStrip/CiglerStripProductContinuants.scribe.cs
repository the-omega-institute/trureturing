using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripProductContinuantsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Dyck path series in a finite strip are quotients of continuants whose denominators are invertible power series.",
        H("Continuants for Bounded Dyck Path Series"),
        Blocks(
            Node("cigler-strip-product-continuants-cont", "The continuant recurrence", "cont",
                "Given a sequence a_n in a commutative ring and initial values r_0 and r_1, the continuant sequence starts with K_0 = r_0 and K_1 = r_1 and satisfies K_{n+2} = K_{n+1} - a_n K_n for every nonnegative integer n. The initial values zero and one give the numerator sequence, while the initial values one and one give the denominator sequence.", DescribeRole.Definition),
            Node("cigler-strip-product-continuants-representation", "A unit denominator and the strip series", "continuant_representation",
                "Let w_k be any sequence of polynomials with integer coefficients, and assume the weighted strip sums obey the first-return convolution for every weight sequence, bound b and semilength n + 1: the sum at height b + 1 is w_0 times the sum over i from zero through n of the height-b sum of semilength i with weights shifted by one times the height-(b + 1) sum of semilength n - i with the original weights. Set a_k = w_k z, and let P and Q be the continuant sequences with initial values (0, 1) and (1, 1), respectively. For every nonnegative height h, Q_{h+1} is an invertible formal power series and Q_{h+1} times the weighted strip series of height h equals P_{h+1}.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
