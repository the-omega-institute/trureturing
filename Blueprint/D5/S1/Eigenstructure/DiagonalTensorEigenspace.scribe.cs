using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class DiagonalTensorEigenspaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ground-valued tensor coefficients characterize the whole eigenspace of a diagonal endomorphism.",
        H("Diagonal Tensor Eigenspaces"),
        Blocks(
            Paragraph(Text(
                "Let K be any field, I and Q arbitrary types, and M and T arbitrary K-vector spaces. "
                + "Choose an algebraic basis b indexed by I for M. Neither I nor either vector space "
                + "is required to be finite. The ground space T may be zero or infinite-dimensional. "
                + "For an endomorphism A of M, its tensor extension is A tensor id on M tensor T. "
                + "The coordinate map C_b is TensorProduct.equivFinsuppOfBasisLeft b: it identifies "
                + "M tensor T with finitely supported functions from I to T. Every algebraic tensor "
                + "has finite support even when the basis is infinite.")),
            Describe.Lean(
                DescribeId.Create("coeff-action"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/DiagonalTensorEigenspace.coeff_action"),
                H("Diagonal action on every tensor coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every basis b, endomorphism A, function a from I to K satisfying "
                    + "A(b_i)=a(i) b_i for every i, every tensor v and every i, the i-th coefficient "
                    + "of (A tensor id)(v) is a(i) times the i-th coefficient of v. First the two "
                    + "scalar coordinate maps b.coord(i) composed with A and a(i) times b.coord(i) "
                    + "agree on every basis element, hence agree on M. Tensor induction then proves "
                    + "the ground-valued identity for pure tensors, zero and sums. The tensor v "
                    + "need not be homogeneous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eigen-iff-supported"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/DiagonalTensorEigenspace.eigen_iff_supported"),
                H("The full eigenvector equation is a support condition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same diagonal-action hypothesis, for every scalar mu and tensor v, "
                    + "(A tensor id)(v)=mu v if and only if C_b(v) belongs to Finsupp.supported T K "
                    + "{i | a(i)=mu}. In the forward direction, a coefficient outside this set is "
                    + "annihilated by the nonzero scalar a(i)-mu, so it is zero. Conversely, inside "
                    + "the set the diagonal scalar equals mu, and outside it both coefficients "
                    + "vanish; injectivity of C_b gives the tensor equation. This includes zero "
                    + "vectors and zero ground spaces without a nonzero premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("graded-eigenspace-equiv"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/DiagonalTensorEigenspace.gradedEigenspaceEquiv"),
                H("A linear equivalence with the complete degree fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every degree map degree:I->Q, injective value map value:Q->K, "
                        + "diagonal action A(b_i)=value(degree(i)) b_i, and q in Q, there is a "
                        + "K-linear equivalence from the eigenspace of A tensor id at value(q) "
                        + "to the finitely supported T-valued functions on {i:I | degree(i)=q}. "
                        + "Injectivity identifies the scalar level set with this degree fibre. "
                        + "The preceding characterization identifies the eigenspace with the "
                        + "inverse image of the supported submodule under C_b; restricting C_b "
                        + "and then applying Finsupp.supportedEquivFinsupp gives the equivalence.")),
                    Paragraph(Text(
                        "The conclusion describes every vector in the eigenspace and retains its "
                        + "linear structure. An empty degree fibre is allowed and gives a zero "
                        + "eigenspace. The label set, degree fibre and ground space can be infinite. "
                        + "No finite-dimensionality, basis cardinality, positivity or nonzero "
                        + "ground assumption is used. Finite-dimensional conclusions require "
                        + "separate hypotheses on the fibre and on T."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "Mathlib supplies the tensor coordinate equivalence, its pure-tensor coefficient "
                + "formula, the supported Finsupp submodule and restriction equivalence, and linear "
                + "equivalence transport. These suppliers are used directly. The scalar-coordinate "
                + "separation architecture also occurs in LatticeActualLZeroGrading.actualL0_coeff "
                + "and actualL0_eigen_iff_grade; LatticeEnergyGrading.gradeCoeffEquiv uses the "
                + "corresponding scalar support restriction. Here the coefficients take values in "
                + "an arbitrary ground space. These connections assert no literature originality "
                + "and impose no lattice or physical interpretation on the generic theorem.")))));
}
