using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class CiglerElevenPolynomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/cigler2023catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebyshev product identities control periodic remainders, reflection and paired rows of the Catalan moment polynomials.",
        H("Polynomial Identities for the Residue Reduction"),
        Blocks(
            Node("cigler-eleven-polynomials-structure", "Periodicity, reflection and monic quotients", "polynomial_structure",
                "Let p_j and h_j be the boundary-weighted Motzkin orthogonal polynomials specialized to interior weight two and boundary weights one and three respectively. Thus p_0 = h_0 = 1, p_1 = X-1, h_1 = X-3, and each family satisfies q_{j+2} = (X-2)q_{j+1}-q_j. Write C_0 = 2, C_1 = X and S_0 = 1, S_1 = X for the Chebyshev families satisfying q_{j+2} = Xq_{j+1}-q_j. For all nonnegative k and j, p_{2k+1+j}-p_j = p_k C_{k+j+1}(X-2). For every nonnegative s at most k, p_{k+s}+p_{k-s} = p_k C_s(X-2). For every positive B and every nonnegative t less than B, p_{B+t}+p_{B-1-t} = X S_{B-1}(X-2) h_t. The recurrence gives p_j = S_j(X-2)+S_{j-1}(X-2) and h_j = S_j(X-2)-S_{j-1}(X-2), with S_{-1} = 0. The product identity C_m S_r = S_{r+m}+S_{r-m} and the identity C_{t+1}(X-2)+C_t(X-2) = Xh_t yield the three formulas.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
