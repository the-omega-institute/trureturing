using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class HalfIntegerBesselPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/HalfIntegerBesselPolynomial.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Analytic/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized half-integer Bessel polynomial and its reflection give an exact Wronskian.",
        H("Half-integer Bessel polynomial and its reflected Wronskian"),
        Blocks(
            Node("coefficient", "Normalized factorial coefficient",
                "For natural m and k with k at most m, the rational coefficient a(m,k) "
                + "is (m+k)! divided by 2^k k! (m-k)!. For k greater than m it is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("carrier", "Finite carrier polynomial",
                "For each natural m the rational polynomial P is the sum of a(m,k) X^k "
                + "for k from zero through m. Its indeterminate corresponds to the reciprocal "
                + "argument of the finite half-integer Bessel carrier.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("coefficient_succ", "Coefficient recurrence",
                "For every natural m and k, 2(k+1) a(m,k+1) equals "
                + "(m-k)(m+k+1) a(m,k), with the factors taken in the rationals. "
                + "The identity includes k=m and all indices above the degree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("carrier_ode", "Differential equation in the reciprocal argument",
                "For every natural m, its carrier P satisfies the rational polynomial "
                + "identity X^2 P'' + (2X+2) P' = m(m+1) P. Each coefficient of this "
                + "identity reduces to the factorial recurrence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("natDegree_carrier", "Degree of the finite carrier",
                "The carrier P_m has natural degree m. Its coefficient at m is nonzero "
                + "and all coefficients at larger indices vanish.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("carrier_coeff_zero", "Carrier constant coefficient",
                "The constant coefficient of the finite reciprocal carrier is one for every order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("reflected_wronskian", "Reflected polynomial Wronskian",
                "For every natural m, let P be its carrier and Q(X) = P(-X). "
                + "Then 2 P Q - X^2 (P Q' - P' Q) = 2 in the rational polynomial ring. "
                + "The two differential equations make the derivative vanish. "
                + "Since P(0) = Q(0) = 1, the constant is 2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("half-integer-bessel-polynomial-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
