using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13SeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Series.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal continuation counts give a generating series with a polynomial old-block variable.",
        H("The actual matching functional equation"),
        Blocks(
            Node("p13-p13series-completionseries", "Single-block completion series", "completionSeries",
                "For each old block size m, the coefficient of z to degree d is the literal completion count c(m,d), cast to the rationals. The variable z marks future closures.", DescribeRole.Definition),
            Node("p13-p13series-actualseries", "The actual matching series", "actualSeries",
                "The coefficient of z to degree n is the number of P13 avoiding perfect matchings on Fin(2n) in the original matching carrier. The empty matching and disconnected matchings are included.", DescribeRole.Definition),
            Node("p13-p13series-countpolynomial", "Finite polynomial at each closure degree", "countPolynomial",
                "At degree d the polynomial is the sum of c(m,d)u to power m for m from zero through d. Support of literal completions removes every larger old block size.", DescribeRole.Definition),
            Node("p13-p13series-completionbivariate", "The bivariate completion series", "completionBivariate",
                "F is the power series in z whose degree d coefficient is countPolynomial(d). Thus F belongs to the ring of power series with rational polynomial coefficients in u.", DescribeRole.Definition),
            Node("p13-p13series-blockmarker", "The old-block variable", "blockMarker",
                "The marker u is the polynomial coefficient variable, embedded as a constant power series in z.", DescribeRole.Definition),
            Node("p13-p13series-reciprocalmarker", "The reciprocal marker", "reciprocalMarker",
                "The reciprocal marker is the unit inverse of 1-zu. It is obtained by rescaling the negative binomial series of exponent one, so its constant coefficient is one.", DescribeRole.Definition),
            Node("p13-p13series-evaluateblock", "Legitimate polynomial substitution", "evaluateBlock",
                "For any v in the polynomial coefficient power series ring, evaluate each polynomial coefficient at v and the outer variable at z. Polynomial evaluation permits a nonzero constant coefficient in v. The outer variable z is topologically nilpotent in the coefficientwise topology, and each resulting z coefficient is a finite sum.", DescribeRole.Definition),
            Node("p13-p13series-completion-functional-equation", "The concrete catalytic functional equation", "completion_functional_equation",
                "For every m, the series f_m has order at least m and its degree m coefficient is one. At every z degree d, the u degree of F is at most d. The exact boundaries are f_0=A and f_0=1+f_1. With v the unit inverse of 1-zu, the equation is (u-1-z*u^2)*F = u-(1+z*u^2)*A+z*u^2*F(v,z). The finite triangular law for literal completions proves the equation coefficient by coefficient. The negative binomial coefficient formula evaluates F(v,z), and the original matching continuation law identifies A. No functional equation or abstract recurrence model is assumed.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
