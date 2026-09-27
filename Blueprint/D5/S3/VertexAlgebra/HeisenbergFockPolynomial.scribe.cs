using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class HeisenbergFockPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational polynomial Fock space carries a concrete Heisenberg field with nonzero center.",
        H("Polynomial Heisenberg Fock Field"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-polynomial-heisenberg-fock-field"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/HeisenbergFockPolynomial.heisenberg_fock_polynomial"),
            H("Shifted polynomial modes satisfy the Heisenberg relation"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let V be the multivariate polynomial ring over the rationals, with one "
                    + "variable X_k for each natural number k and vacuum 1. The mode a_(k+1) "
                    + "is (k+1) times partial differentiation with respect to X_k, the mode "
                    + "a_(-(k+1)) multiplies by X_k, and a_0 is zero. These modes are "
                    + "rational-linear endomorphisms of V.")),
                Paragraph(Text(
                    "The constructed Mathlib VertexOperator A has normalized coefficient "
                    + "A[[m]] = a_m for every integer m. For each polynomial p, there is an "
                    + "integer B such that A[[m]] p is zero for all m greater than B. "
                    + "This pointwise bound makes the Laurent coefficient construction valid.")),
                Paragraph(Text(
                    "For every pair of integers m and n, the operator commutator "
                    + "A[[m]] composed with A[[n]] minus A[[n]] composed with A[[m]] "
                    + "equals m times the identity when m+n=0, and zero otherwise. "
                    + "Its value on vacuum 1 at (m,n)=(1,-1) is 1, so the center acts "
                    + "nontrivially. Every X_k is A[[-(k+1)]] applied to 1. The rational "
                    + "linear span of all finite words of negative modes applied to 1 is V.")),
                Paragraph(Text(
                    "The mixed commutator follows from the polynomial Leibniz rule and "
                    + "partial derivative of X_j. Partial derivatives commute and multiplication "
                    + "operators commute. Chu and Lin, Moduli spaces of conformal structures "
                    + "on Heisenberg vertex algebras, arXiv:1812.11378v1, Section 3.1, "
                    + "describe the standard complex Fock construction and mode bracket. "
                    + "The rational polynomial realization and its pointwise Laurent support "
                    + "are established here."))),
            DescribeRole.Theorem))));
}
