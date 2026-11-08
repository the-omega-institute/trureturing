using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class TraceDualSkewMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/TraceDualSkewMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace-dual coordinates for an arbitrary semilinear Galois algebra.",
        H("Trace-dual Galois Skew Matrices"),
        Blocks(
            Paragraph(Text("Let F/k be a finite Galois extension and let A be any unital "
                + "F-algebra, with a compatible k-algebra structure and a multiplicative "
                + "semilinear action of Gamma = Gal(F/k). The universes of k, F, A and "
                + "the basis index are independent. The algebra A may be noncommutative "
                + "or trivial, and need not be finite dimensional. No inverse of the "
                + "group order or descent hypothesis is assumed.")),
            Entry("invariants", "Fixed algebra and right module", DescribeRole.Definition,
                "The k-subalgebra C consists of the elements fixed by every g in Gamma. "
                + "The right C-module A is implemented as a left module over C-op: "
                + "the scalar op(c) sends x to x*c. The action commutes with k-scalars "
                + "because it is semilinear over the given Galois action on F."),
            Entry("Phi_apply", "Canonical skew action", DescribeRole.Theorem,
                "Phi(r)(x) = sum_g r.coeff(g)*(g acting on x). Coefficients act by left "
                + "multiplication and group elements act by the supplied action. "
                + "Mathlib's liftNCAlgHom constructs the algebra homomorphism. Its "
                + "forward map contains no choice of a field basis."),
            Entry("d", "Trace-dual invariant coordinates", DescribeRole.Definition,
                "Choose a finite k-basis b of F and its trace-dual basis. Write u_i for "
                + "the image of b_i in A and v_i for the image of its trace-dual element. "
                + "The coordinate d_i(x) is sum_g g acting on (v_i*x), as an element "
                + "of C. Left translation permutes Gamma, proving fixedness, and "
                + "d_i(x*c) = d_i(x)*c proves right C-linearity."),
            Entry("d_basis_mul", "Coordinate delta identity", DescribeRole.Theorem,
                "For every c in C, d_j(u_i*c) equals c when j=i and zero otherwise. "
                + "This follows from the trace-dual pairing and the expression of "
                + "Galois trace as a sum of automorphisms."),
            Entry("reconstruct", "Reconstruction", DescribeRole.Theorem,
                "Every x in A satisfies sum_i u_i*d_i(x) = x. Over F, the matrices "
                + "P[g,i] = g(b_i) and Q[i,g] = g(traceDual_i) satisfy QP=1 by the "
                + "trace pairing. Their equal finite dimensions give PQ=1 by the "
                + "existing field matrix inverse theorem. The resulting "
                + "automorphism orthogonality transports through F to A. Stable "
                + "finiteness is used only over the field F."),
            Entry("coordinates", "Actual invariant module coordinates", DescribeRole.Definition,
                "The maps x mapped to (d_i(x)) and c mapped to sum_i u_i*c_i are inverse "
                + "C-op-linear maps between A and the functions I to C. Reconstruction "
                + "and the coordinate delta identity prove the two inverse laws."),
            Entry("rightBasis", "Genuine right invariant basis", DescribeRole.Definition,
                "Pointwise op turns the coordinate functions into functions I to C-op. "
                + "Mathlib's Basis.ofEquivFun then gives a genuine C-op-basis of A, "
                + "whose ith vector is u_i. The basis is constructed rather than assumed."),
            Entry("Psi_coeff", "Explicit inverse coefficients", DescribeRole.Theorem,
                "Psi(T).coeff(g) = sum_i T(u_i)*(g acting on v_i). This order of "
                + "multiplication is retained when A is noncommutative."),
            Entry("Phi_Psi", "Endomorphism inverse law", DescribeRole.Theorem,
                "Phi(Psi(T)) = T for every endomorphism of the right C-module A. "
                + "The coefficient formula, finite sum interchange and right "
                + "C-linearity reduce this law to invariant-coordinate reconstruction."),
            Entry("Psi_Phi", "Skew coefficient inverse law", DescribeRole.Theorem,
                "Psi(Phi(r)) = r for every element of the skew monoid algebra. "
                + "At each group coefficient, finite sum interchange and the "
                + "transported automorphism orthogonality give the original coefficient."),
            Entry("skewEndEquiv", "Canonical skew and endomorphism equivalence", DescribeRole.Definition,
                "The canonical k-algebra equivalence identifies SkewMonoidAlgebra A Gamma "
                + "with Module.End C-op A. A field basis supplies its inverse proof; "
                + "the forward homomorphism remains exactly Phi. The theorem "
                + "skewEndEquiv_symm_coeff gives its inverse coefficient formula "
                + "using any finite k-basis of F."),
            Entry("endMatrixEquiv_apply", "Ordinary matrix entries", DescribeRole.Theorem,
                "The endomorphism T has matrix entry (j,i) equal to d_j(T(u_i)). "
                + "Conjugation by the actual invariant coordinates and Mathlib's "
                + "endomorphism matrix equivalence reduce to matrices over End C-op C. "
                + "The existing moduleEndSelfOp equivalence converts those entries "
                + "to C itself, so the matrix coefficient ring is C."),
            Entry("skewMatrixEquiv", "Basis-dependent matrix presentation", DescribeRole.Definition,
                "For the chosen field basis b, the skew algebra is k-algebra equivalent "
                + "to ordinary Matrix I I C. This matrix presentation depends on b. "
                + "It makes no normalized-rank, inner-action, Schur, Frobenius-bound "
                + "or literature-novelty assertion."),
            Entry("skewMatrixEquiv_apply", "Skew matrix coefficient formula", DescribeRole.Theorem,
                "The (j,i) entry of the matrix of r is "
                + "d_j(sum_g r.coeff(g)*(g acting on u_i))."))));

    private static DocumentBlock.Describe Entry(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
