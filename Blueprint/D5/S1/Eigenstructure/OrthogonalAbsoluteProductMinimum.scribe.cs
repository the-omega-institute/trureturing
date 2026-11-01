using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class OrthogonalAbsoluteProductMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonsingular real square matrix has orthogonal absolute-product minimum exactly one, attained by a Gram-Schmidt basis.",
        H("Orthogonal Absolute-Product Minimum"),
        Blocks(
            Paragraph(Text("Source: User3 (MathOverflow user 600125), A nontrivial lower bound for the orthogonally transformed absolute product, MathOverflow question 515549, https://mathoverflow.net/questions/515549, revision 1 CB719581-BCE3-4573-931E-15327002F861, published 2026-09-25T19:17:56+00:00, CC BY-SA 4.0. The source asks whether a bound beta(P)>1 can hold for every orthogonal Q for a class of nonsingular P, and asks to characterize the infimum. The theorem below characterizes that value as the attained constant one. The derivation is an application of the cited library results; no claim of worldwide novelty or all-minimizer classification is made.")),
            Describe.Lean(DescribeId.Create("entry-abs"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.entryAbs"),
                H("Entrywise absolute value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural K and real K-by-K matrix A, entryAbs(A) has entry (i,j) equal to the real absolute value of A(i,j). This operation does not denote a matrix norm or the positive square root of a matrix product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radius"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.radius"),
                H("Complex spectral radius of a real matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural K and real K-by-K matrix A, radius(A) is the complex spectral radius after entrywise inclusion of the real entries into the complex numbers. Lean's spectralRadius has extended nonnegative real values; toReal converts it to a real number. Finite matrices have finite spectral radius, by spectrum.spectralRadius_le_nnnorm, so this conversion retains the usual spectral radius. For positive K it is the maximum modulus of the complex eigenvalues, including multiplicity only insofar as it determines the spectrum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orthogonal"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.Orthogonal"),
                H("The full real orthogonal domain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural K, Orthogonal(Q) asserts both transpose(Q) times Q equals the identity and Q times transpose(Q) equals the identity. All products are ordinary square-matrix products."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("objective"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.objective"),
                H("The source objective"), StatementSource.FromAuthor(ObjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural K and real K-by-K matrices P and Q, the objective is the complex spectral radius of entryAbs(PQ) times entryAbs(transpose(Q) times inverse(P)). Inverse is the ordinary matrix inverse when det(P) is nonzero; the result uses exactly that nonsingular domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result"),
                H("Universal lower bound and an attaining orthogonal matrix"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive integer K and every real K-by-K matrix P with nonzero determinant, every orthogonal Q has objective at least one, and there exists an orthogonal Q with objective exactly one. No upper bound on dimension, matrix sign condition, approximation, norm substitute or diagonalizability hypothesis is imposed. The existence clause is an actual attained equality, not only an infimum statement.")),
                    Paragraph(Text("For arbitrary orthogonal Q, set A=PQ and B=transpose(Q) times inverse(P). Their product is the identity. The finite-sum triangle inequality gives identity <= entryAbs(A) entryAbs(B) entrywise. D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono compares their spectral radii and gives the universal bound.")),
                    Paragraph(Text("Apply InnerProductSpace.gramSchmidtOrthonormalBasis to the ordered rows of P in real Euclidean K-space, and place this orthonormal basis in the columns of Q. Mathlib's basis-change identities give both orthogonality equations. Its gramSchmidtOrthonormalBasis_inv_triangular theorem makes T=PQ lower triangular. Nonsingularity and orthogonality identify inverse(T) with transpose(Q) times inverse(P). Matrix.blockTriangular_inv_of_blockTriangular gives the same triangular orientation for that inverse.")),
                    Paragraph(Text("The absolute values retain the triangular zeros. In a diagonal entry of a product of two lower triangular matrices, only the matching diagonal term survives. Since T times inverse(T) is the identity, each diagonal entry of entryAbs(T) entryAbs(inverse(T)) is one. The product remains lower triangular. After complexification, transpose and Matrix.charpoly_of_isUpperTriangular give characteristic polynomial (X-1)^K. Matrix.mem_spectrum_iff_isRoot_charpoly and K>0 identify the spectrum with the singleton {1}; spectralRadius_eq_of_unital gives radius one, without any diagonalizability assumption.")),
                    Paragraph(Text("Consequently the minimum, and hence the infimum, of the source objective over the entire orthogonal group is one. A strict lower bound beta(P)>1 uniform over that group is impossible for any nonsingular P, and therefore for any nonempty class of them. These are mathematical consequences of the displayed two-clause theorem; no separate companion result is introduced."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("user3-2026-orthogonal-absolute-product-minimum"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula ObjectiveFormula()
    {
        Formula k = F.Id("K"), p = F.Id("P"), q = F.Id("Q");
        return Disp(Seq(Forall, Sp, k, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Forall, Sp, p, Comma, q, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(F.Id("R")), Caret, Grp(k, Sp, Times, Sp, k)), Comma, Esc,
            Call("objective", p, q), Sp, Eq, Sp,
            Call("rho", Seq(Abs(Seq(p, q)), Sp,
                Abs(Seq(q, Caret, Grp(F.Id("T")), Sp, p, Caret, Grp(Minus, D(1))))))));
    }
    private static Formula ResultFormula()
    {
        Formula k = F.Id("K"), p = F.Id("P"), q = F.Id("Q");
        Formula orth = Call("O", k);
        return Disp(Seq(Forall, Sp, k, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))),
            Comma, Sp, k, Sp, Gt, Sp, D(0), Comma, Esc,
            Forall, Sp, p, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R")), Caret, Grp(k, Sp, Times, Sp, k)),
            Comma, Sp, Call("det", p), Sp, Neq, Sp, D(0), Sp, Rightarrow, Esc,
            Open, Forall, Sp, q, Sp, InMacro, Sp, orth, Comma, Sp,
            Call("objective", p, q), Sp, Ge, Sp, D(1), Close, Sp, Land, Esc,
            Open, Exists, Sp, q, Sp, InMacro, Sp, orth, Comma, Sp,
            Call("objective", p, q), Sp, Eq, Sp, D(1), Close));
    }
}
