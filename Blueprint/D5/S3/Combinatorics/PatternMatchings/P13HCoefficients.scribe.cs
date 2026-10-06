using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13HCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient extraction from the actual catalytic H proves its boundary laws, bulk recurrence and minimal-solution identity.",
        H("Actual H coefficients and boundary elimination inputs"),
        Blocks(
            Paragraph(Text("The declarations live in D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH. The outer variable X marks formal series degree; t is the polynomial coefficient marker. H is the lawful transform of the literal completion series from the original ordinary perfect-matching carrier. Its rows are extracted from this H, not defined by a recurrence. All series are formal over the rationals; the discrete coefficient topology justifies evaluation and coefficientwise sums.")),
            Node("p13-hcoefficients-scalar-embed", "Embedding rational series", "scalarEmbed",
                "scalarEmbed maps each rational coefficient to a constant polynomial. This ring homomorphism relates the ordinary series A to the polynomial-coefficient series Aq.", DescribeRole.Definition),
            Node("p13-hcoefficients-row", "Transposed polynomial coefficients", "row",
                "For any f in Rational[t][[X]], coeff n (row k f) is the coefficient of t^k in coeff n f. Each row is a rational power series.", DescribeRole.Definition),
            Node("p13-hcoefficients-row-shift", "Diagonal action of t to Xt", "row_shift",
                "For every k and polynomial-coefficient series f, row k (shift f) = X^k row k f. The proof reduces legitimate coefficient evaluation to a finite sum of polynomial monomials, then isolates the coefficient at n-k. This finite-series calculation is used in every actual H boundary and bulk extraction.", DescribeRole.Theorem),
            Node("p13-hcoefficients-h", "Rows of the actual H", "h",
                "h(k) is row k H. It retains the literal completion carrier through H's lawful change of variables.", DescribeRole.Definition),
            Node("p13-hcoefficients-z", "Lawful outer substitution", "Z",
                "Z=X invPlus^2, where invPlus is the formal unit inverse of 1+X. Z has zero constant coefficient; Z_hasEval and Z_clear justify evaluation and prove Z(1+X)^2=X.", DescribeRole.Definition),
            Node("p13-hcoefficients-a", "The actual counting series at Z", "A",
                "A is actualSeries evaluated at Z through the continuous constant embedding and proved HasEval Z. The original actualSeries counts every P13-avoiding fixed-point-free involution of Fin(2n), including empty and disconnected matchings.", DescribeRole.Definition),
            Node("p13-hcoefficients-aq-actual", "Identifying the embedded actual series", "Aq_actual",
                "Aq equals scalarEmbed A. Two lawful coefficientwise HasSum evaluations and continuity of scalarEmbed establish this identity. The expanded H equation uses it before taking rows.", DescribeRole.Theorem),
            Node("p13-hcoefficients-boundary-zero", "Boundary at t degree zero", "h_boundary_zero",
                "X h(0) = (1+X)(A-1). This equation comes from row zero of the actual catalytic H equation.", DescribeRole.Theorem),
            Node("p13-hcoefficients-boundary-one", "Boundary at t degree one", "h_boundary_one",
                "X^2 h(1) + ((1-X)^2-2X) h(0) = (1+X)^2-4XA. This equation comes from row one of the same actual equation.", DescribeRole.Theorem),
            Node("p13-hcoefficients-boundary-two", "Boundary at t degree two", "h_boundary_two",
                "X^3 h(2) + ((1-X)^2-2X^2) h(1) + X(1-X)h(0) = 0. The X(1-X)h(0) term is retained: row two and X times the degree-zero boundary give this exact law.", DescribeRole.Theorem),
            Node("p13-hcoefficients-bulk", "The actual all-index bulk law", "h_bulk",
                "For every j at least two, X^(j+2)h(j+1) + ((1-X)^2-2X^(j+1))h(j) + X^j h(j-1) = 0. Extracting row j+1 proves it on the actual H family; no Bulk hypothesis is assumed.", DescribeRole.Theorem),
            Node("p13-hcoefficients-divisibility", "Structural divisibility of actual rows", "h_dvd",
                "For every natural k, X^k divides h(k). The proof constructs a quotient from the actual degree-two boundary for k=1 and from h_bulk for k at least two, cancelling only the unit (1-X)^2. This is an additional structural support law for the transformed actual series. The final enumeration uses the boundary and bulk laws directly and does not need this divisibility statement.", DescribeRole.Theorem),
            Node("p13-hcoefficients-actual-bulk", "Discharging the scalar Bulk contract", "actual_Bulk",
                "The actual family h satisfies P13Scalar.Bulk by h_bulk. This consumed adapter supplies the proved premise of h_minimal_solution; it is not additional mathematical content.", DescribeRole.Theorem),
            Node("p13-hcoefficients-minimal", "Minimality on the actual H family", "h_minimal_solution",
                "For every j at least two, (1-X)^2 Phi(j)h(j) + X^j Phi(j+1)h(j-1) = 0. The scalar uniform annihilation theorem applies with actual_Bulk. P13Enumeration.actual_A_eq_G consumes this identity at j=2 together with all three actual boundaries and Phi_difference at j=1, discharging every boundary-elimination premise.", DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/PatternMatchings/P13CatalyticH")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/PatternMatchings/P13Scalar"))
        ]));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
