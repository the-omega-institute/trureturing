using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentCatalanPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordinary ascent words with literal adjacent-pair avoidance and exact boundary conditions.",
        H("Actual ordinary-avoider peak polynomials"),
        Blocks(
            Node("wordpeakpolynomial", "wordPeakPolynomial", "wordPeakPolynomial",
                "The finite sum of y raised to n minus strict ascents over the actual length-n ordinary words avoiding literal 10-1 and 20-1.", DescribeRole.Definition),
            Node("dyckpeakpolynomial", "dyckPeakPolynomial", "dyckPeakPolynomial",
                "The finite sum of y raised to the adjacent UD peak count over actual Mathlib Dyck words of semilength n.", DescribeRole.Definition),
            Node("wordpeakpolynomial-eq", "wordPeakPolynomial_eq", "wordPeakPolynomial_eq",
                "The proved actual equivalence transports the entire finite weighted sum from ordinary avoiders to the Dyck peak polynomial.", DescribeRole.Theorem),
            Node("coeff-dyckpeakpolynomial", "coeff_dyckPeakPolynomial", "coeff_dyckPeakPolynomial",
                "Every coefficient of the Dyck peak polynomial is the cardinality of the corresponding actual peak fiber.", DescribeRole.Theorem),
            Node("coeff-wordpeakpolynomial", "coeff_wordPeakPolynomial", "coeff_wordPeakPolynomial",
                "The actual ordinary-word weighted polynomial has Narayana coefficients whenever (n,k) is not (1,0). This explicitly retains the licensed supplier boundary.", DescribeRole.Theorem),
            Node("coeff-one-zero", "coeff_one_zero", "coeff_one_zero",
                "The actual semilength-one zero-peak coefficient is zero, separately handling the natural quotient exception.", DescribeRole.Theorem),
            Node("eval-one", "eval_one", "eval_one",
                "Evaluation of the actual ordinary-word weighted polynomial at one recovers the Catalan total at every n, including zero. The formal-series functional equation and Lagrange inversion over Q[y] remain separate obligations.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ordinaryascentcatalanpolynomial-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
