using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class PolynomialKernelRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete entire rank-three profile classification.",
        H("The complete entire rank-three profile classification"),
        Blocks(Describe.Lean(DescribeId.Create("entire-weighted-hankel-rank-three"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/PolynomialKernelRank.separated_three_iff_profile"),
            H("The complete entire rank-three profile classification"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every nonzero entire complex f, the kernel (z-w)^2*f(z+w) has at most three entire separated terms exactly when f(z)=c*exp(alpha*z) or f(z)=c*exp(alpha*z)*(z-beta)^2 for complex c, alpha and beta with c nonzero. Both directions and all complex coefficients are included.")),
                Paragraph(Text("Finite separation first gives a finite exponential-polynomial presentation. Algebraic block projections in both variables isolate a block diagonal four-by-four evaluation minor whenever two distinct nonzero exponent blocks occur: one block supplies a nonzero three-point minor and the other a nonzero entry. Any three-term separation would bound this matrix rank by three, a contradiction.")),
                Paragraph(Text("For a polynomial of degree at least three, Hasse-Taylor coefficient rows give a triangular four-by-four minor using rows 0,1,2,3, except that degree seven uses row four in place of row three. Nonzero top weights prove the obstruction for every degree, without a finite degree cutoff. A genuine linear polynomial has a four-by-four minor with determinant B^4.")),
                Paragraph(Text("For a genuine quadratic A+B*z+C*z^2, the coefficient minor on indices 0,1,2,4 has determinant C^2*(B^2-4*A*C). Thus separation at most three forces the complex discriminant to vanish. Conversely a zero discriminant gives a complex shifted square. Multiplication by an exponential preserves the exact separation bound. The probes extend linearly from polynomials to all functions, so no polynomial-factor hypothesis is imposed on a proposed entire separation."))),
            DescribeRole.Theorem))));
}

