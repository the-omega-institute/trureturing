using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class QuarterPowerSqrtHilbertSchmidtDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp quarter-power square-root estimates, bounded congruence, and compact coercivity.",
        H("Quarter-power Hilbert–Schmidt bounds for positive square roots"),
        Blocks(
            Paragraph(Text("Stage 3A of issue #34535. The operator estimate supplies the square-root trace step "
                + "for Eq. (71) of Satishchandran and Sorce when the covariance operators admit the required "
                + "quarter-power factorization.")),
            Entry("quarter-root", "quarterRoot", "Quarter root",
                "The quarter root of an operator is the continuous-functional-calculus square root of its square root.",
                DescribeRole.Definition),
            Entry("adjoint-congruence", "adjointCongr", "Rectangular adjoint congruence",
                "For C from K to H and an endomorphism A of H, congruence is the endomorphism C* A C of K.",
                DescribeRole.Definition),
            Entry("hilbert-schmidt-square", "hsSq", "Squared Hilbert–Schmidt norm",
                "Given a proof that W is Hilbert–Schmidt, sum the squared norms of its columns in a chosen Hilbert basis. "
                + "Parseval identifies the sum in every Hilbert basis.", DescribeRole.Definition),
            Entry("rectangular-factor", "exists_bounded_factor", "Factor through a bounded endomorphism",
                "If L maps K into H, D acts on K, c is nonnegative and ‖Lx‖ ≤ c ‖Dx‖ for every x, "
                + "then L = ZD for a bounded map Z from K into H with ‖Z‖ ≤ c. "
                + "Extend from the range of D to its closure and compose with orthogonal projection."),
            Entry("rectangular-ideal-estimate", "adjointCongr_hsSq_le", "Rectangular Hilbert–Schmidt estimate",
                "Congruence of a Hilbert–Schmidt W by a bounded map Z is Hilbert–Schmidt. "
                + "Its squared norm is at most ‖Z‖⁴ times that of W. Rectangular Parseval transfers the column sum to the adjoint."),
            Entry("quarter-power-congruence", "quarterPower_congruence", "Quarter-power factorization under congruence",
                "For positive A and B with B − A = A^(1/4) W A^(1/4) and W Hilbert–Schmidt, set M = C* A C. "
                + "There is Z with ‖Z‖² ≤ ‖C‖ and A^(1/4) C = Z M^(1/4). The congruence of B − A equals "
                + "M^(1/4) (Z* W Z) M^(1/4), and Z* W Z is Hilbert–Schmidt with squared norm at most ‖C‖² times that of W."),
            Entry("finite-quarter-power-estimate", "finite_quarterPower_sqrt_hsSq_le", "Finite-dimensional sharp estimate",
                "If A and B are positive, W is Hilbert–Schmidt and B − A = A^(1/4) W A^(1/4), the squared Hilbert–Schmidt norm of "
                + "√B − √A is at most that of W. For invertible A, express both squared Hilbert–Schmidt norms as traces and use cyclicity. "
                + "In an eigenbasis of √B, Cauchy–Schwarz gives k ≥ 1/p for the inverse-quarter-root column square k, "
                + "where p is the quarter-root column square. For each eigenvalue r the remainder is bounded below by "
                + "r(r − p)²(r + 2p)/p². Scalar regularization and polynomial approximation cover singular A."),
            Entry("quarter-power-sharpness", "quarterPower_sqrt_sharp", "Equality on the scalar Hilbert space",
                "For A = 1, B = 0, and W = −1 on ℂ, the quarter-power factorization holds and both squared "
                + "Hilbert–Schmidt norms are one."),
            Entry("quarter-power-estimate", "quarterPower_sqrt_hsSq_le", "Sharp estimate on arbitrary Hilbert spaces",
                "For positive A and B with B − A = A^(1/4) W A^(1/4) and W Hilbert–Schmidt, √B − √A "
                + "is Hilbert–Schmidt with squared norm at most that of W. Compress over finite subsets of a Hilbert basis, "
                + "zero-extend the square roots and pass the uniform bound on each finite column sum to the strong limit."),
            Entry("quarter-power-norm", "quarterPower_sqrt_hsNorm_le", "Norm bounds",
                "Under the quarter-power factorization, the Hilbert–Schmidt norm of √B − √A is at most that of W "
                + "and hence at most √2 times that of W."),
            Entry("quarter-power-trace-class", "quarterPower_sqrt_sq_isTraceClass", "Trace class of the squared root difference",
                "Under the quarter-power factorization, the square of √B − √A is trace class by the product theorem "
                + "for two Hilbert–Schmidt operators."),
            Entry("quarter-power-congruence-estimate", "quarterPower_congruence_sqrt_hsSq_le", "Sharp estimate after congruence",
                "The difference between the square roots of C* B C and C* A C is Hilbert–Schmidt, with squared norm "
                + "at most ‖C‖² times that of W under the quarter-power factorization."),
            Entry("compact-coercivity", "compact_add_one_coercive", "Compact coercivity",
                "If T is compact and T and J are self-adjoint, ker J = {0}, and 1 + T ± J are positive, "
                + "then N = 1 + T has trivial kernel and satisfies c I ≤ N for some c > 0. "
                + "Use the signed quadratic forms to rule out a −1 eigenvector of T, then apply the compact lower bound."),
            Entry("hilbert-schmidt-coercivity", "hilbertSchmidt_add_one_coercive", "Hilbert–Schmidt coercivity",
                "The compact coercivity conclusion holds under the same self-adjointness, signed positivity, and kernel "
                + "hypotheses when T is Hilbert–Schmidt."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
