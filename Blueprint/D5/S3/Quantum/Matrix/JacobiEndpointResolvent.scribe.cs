using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class JacobiEndpointResolventDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/JacobiEndpointResolvent";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first Green column of a finite tridiagonal matrix factors along the path.",
        H("Jacobi endpoint resolvent"),
        Blocks(
            Item("Tail", "Tail index type",
                "For a site i in Fin n, the tail contains precisely the sites j with i≤j.",
                DescribeRole.Definition),
            Item("tailFirst", "First tail site",
                "The first site of the tail starting at i is i viewed in the tail index type.",
                DescribeRole.Definition),
            Item("tail", "Principal compression",
                "For a square matrix A indexed by Fin n, tail(A,i) restricts both indices to the tail starting at i.",
                DescribeRole.Definition),
            Item("spectralShift", "Shifted matrix",
                "For a square matrix H and a scalar z over the same field, the shifted matrix is A=zI−H.",
                DescribeRole.Definition),
            Item("IsTridiagonal", "Tridiagonal support",
                "An entry vanishes whenever its row and column indices differ by more than one.",
                DescribeRole.Definition),
            Item("bond", "Lower bond",
                "The bond b_j is H(j+1,j) when j has a successor. The terminal site has bond value zero.",
                DescribeRole.Definition),
            Item("bondProduct", "Intervening bond product",
                "The product at i ranges over j<i and is one at i=0.",
                DescribeRole.Definition),
            Item("tailDiagonal", "Leading inverse tail entry",
                "For a square matrix A and a site i, m_i(A) is the first diagonal entry of the nonsingular inverse of tail(A,i).",
                DescribeRole.Definition),
            Item("tailDiagonalProduct", "Inverse tail product",
                "The inverse tail product at i multiplies m_j(A) over all j≤i.",
                DescribeRole.Definition),
            Item("firstColumn", "First inverse column",
                "In positive dimension, g(A) is the column at site zero of the nonsingular inverse of A.",
                DescribeRole.Definition),
            Item("firstColumn_step", "Transfer across one bond",
                "Let H be tridiagonal over a field, with every principal tail of A=zI−H invertible. "
                + "For consecutive sites p,i with i=p+1, g(A)_i=b_p g(A)_p m_i(A). "
                + "On rows in the tail starting at i, the equation A g=e_0 has zero right-hand side. "
                + "The prefix contributes only at the first row of that tail, where the shifted matrix entry is −b_p. "
                + "Solving the tail equation gives the stated coordinate, including the case b_p=0."),
            Item("firstColumn_eq", "First Green column product",
                "Under the same tridiagonal support and tail invertibility assumptions, for every site i in "
                + "positive dimension, g(A)_i is the product of b_j over j<i times the product of m_j(A) over j≤i. "
                + "At site zero the full tail is a reindexing of A. The successor step multiplies the earlier "
                + "coordinate by the new bond and leading inverse entry."),
            Item("tailDiagonal_ne_zero", "Leading inverse entry is nonzero",
                "For any square matrix A over a field with invertible principal tails, every m_i(A) is nonzero. "
                + "If the leading entry of the inverse column were zero, the restriction to the next tail would "
                + "solve a homogeneous equation and vanish by invertibility. The same conclusion holds at the "
                + "terminal site because the tail has just one coordinate. In either case the column equation "
                + "requires unit input at the first tail site."),
            Item("firstColumn_eq_zero_iff", "Vanishing detects an intervening zero bond",
                "Under tridiagonal support and tail invertibility, g(zI−H)_i vanishes if and only if some bond "
                + "b_j with j<i vanishes. The inverse tail product has no zero factors. Since the scalars form "
                + "a field, the remaining finite product is zero exactly when one of its factors is zero."),
            Item("supported_mulVec_firstColumn", "Action of a supported perturbation",
                "Under the same assumptions on H and z, let W have columns indexed by Fin n and arbitrary row "
                + "type. For any natural k, suppose W has zero columns at all sites j with k≤j. Then W times "
                + "the first inverse column of zI−H is the sum over j<k in Fin n of W's j-th column scaled "
                + "by the intervening bond product and the inverse tail product at j. The finite filter also "
                + "covers k=0 and k>n. This is the column identity used for the supported perturbation "
                + "in the fixed-collar Petz recovery argument."))));

    private static DocumentBlock Item(string name, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name == "Tail" ? "tail-index-type" : name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
