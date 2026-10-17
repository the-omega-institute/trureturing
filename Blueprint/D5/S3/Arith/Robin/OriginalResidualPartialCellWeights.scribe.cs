using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalResidualPartialCellWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalResidualPartialCellWeights.";

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(
            DescribeId.Create("original-partial-cell-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact real partial cells define an affine Gram projection with two zero moments and explicit mass and complete zero-extension variation bounds.",
        H("The Original Partial-Cell Projection"),
        Blocks(
            Paragraph(Text(
                "Let N be a natural number at least 3, with real N<a<b<2N. "
                + "Write lambda(t)=1/(t log(t)), k(t)=(log(t)+1)/(t^2 log(t)^2), "
                + "and S={N,...,2N-1}. Block sums below use this same S. "
                + "The integral retains the literal real endpoints and all partial cells. "
                + "Coefficients c0 and c1 are real and have no sign restriction.")),
            Definition("omega", "Exact intersection mass",
                "For real a,b and natural m, omega(a,b,m) is the Lebesgue integral of k(t) "
                + "over [a,b] intersect [m,m+1]. Empty and singleton intersections have zero mass."),
            Definition("w", "Discrete weight",
                "For natural m, w(m)=1/[m(m+1)], using real division."),
            Definition("v", "Affine sample",
                "For natural N,m, v(N,m) is the real two-vector (1,m/N)."),
            Definition("gram", "Actual finite Gram",
                "For natural N and i,j in Fin 2, G(N)[i,j]=sum_(m in S) w(m)v(N,m)[i]v(N,m)[j]."),
            Definition("datum", "Original cell datum and terminal value",
                "For natural N,m and real a,b, d(N,a,b,m)=log(N)omega(a,b,m)/w(m) "
                + "when m is different from 2N, and d(N,a,b,2N)=0."),
            Definition("rhs", "Actual normal-equation right side",
                "For natural N, real a,b and i in Fin 2, h(N,a,b)[i]=sum_(m in S) "
                + "w(m)d(N,a,b,m)v(N,m)[i]."),
            Definition("delta", "Gram determinant",
                "For natural N, Delta(N)=G(N)[0,0]G(N)[1,1]-G(N)[0,1]^2."),
            Definition("c", "Actual Cramer coefficients",
                "For natural N and real a,b, c0=(G11*h0-G01*h1)/Delta and "
                + "c1=(G00*h1-G01*h0)/Delta, with all entries taken at those same N,a,b."),
            Definition("residual", "Affine residual with a separate terminal value",
                "For natural N,m and real a,b, r(N,a,b,m)=d(N,a,b,m)-c0-c1*m/N "
                + "when m is different from 2N. Its value at 2N is separately zero."),
            Definition("coeff", "Zero-extended projected coefficient",
                "For natural N,m and real a,b, A(N,a,b,m)=w(m)r(N,a,b,m) for N<=m<2N, "
                + "and is zero elsewhere."),
            Definition("mass", "Absolute coefficient mass",
                "For natural N and f from the naturals to the reals, mass(N,f)=sum_(m in S)|f(m)|."),
            Definition("variation", "Both boundary jumps",
                "For natural N and f from the naturals to the reals, "
                + "variation(N,f)=|f(N)|+sum_(N<=m<2N-1)|f(m+1)-f(m)|+|f(2N-1)|. "
                + "For N>=1, this is the complete variation of the finite sequence extended by zero."),
            Definition("harmonic", "Exact harmonic factor",
                "For natural N, J(N)=sum_(m in S)1/(m+1), equivalently sum_(N<j<=2N)1/j."),
            Describe.Lean(
                DescribeId.Create("original-partial-cell-projection-bounds"),
                DeclarationHandle.Create(Prefix + "or6_partialCell_variation"),
                H("Exact projection, two moments, mass and variation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N>=3 and real N<a<b<2N, put ell_m=max(a,m), "
                        + "u_m=min(b,m+1). For every natural m, omega_m=lambda(ell_m)-lambda(u_m) "
                        + "if ell_m<u_m, and omega_m=0 otherwise. The actual Delta(N) is strictly "
                        + "positive, c=G^(-1)h, and Gc=h. The actual coefficients satisfy "
                        + "sum_(m in S) A_m=0 and sum_(m in S)m*A_m=0. "
                        + "The three terminal values d(2N), r(2N) and A(2N) are zero.")),
                    Paragraph(Text(
                        "Write L=log(N), V=variation(N,A), and M=mass(N,A). Then "
                        + "V<=2L*k(a)+2(|c0|+|c1|)/[N(N+1)] "
                        + "<=2L*k(N)+2(|c0|+|c1|)/[N(N+1)], and "
                        + "M<=L[lambda(a)-lambda(b)]+|c0|/(2N)+|c1|J(N)/N.")),
                    Paragraph(Text(
                        "The normal equations follow from the positive actual finite Gram: "
                        + "a nonzero affine polynomial cannot vanish at both samples N and N+1. "
                        + "The cell integral is evaluated with the existing reciprocal-logarithm "
                        + "density-integral theorem. For the variation estimate, the truncated density "
                        + "is the difference of two decreasing functions, a capped density and its "
                        + "constant left step. Averaging over a unit cell preserves their decrease. "
                        + "The finite difference sum telescopes with both endpoint jumps and is at "
                        + "most 2k(a). Both decreasing discrete sequences w(m) and (m/N)w(m) "
                        + "have complete variation 2/[N(N+1)]. Their masses are 1/(2N) and J(N)/N. "
                        + "Triangle inequalities apply to the same signed coefficients.")),
                    Paragraph(Text(
                        "This is a finite coefficient construction. It supplies the two moments "
                        + "and explicit absolute bounds for the unchanged residual. It does not "
                        + "establish a signed residual estimate, compensation of the affine observations, "
                        + "analytic spectral suppliers, the original infinite construction, strict Robin "
                        + "for all integers above 5040, or the Riemann hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-partial-cell-energy-bound"),
                DeclarationHandle.Create(Prefix + "or6_partialCell_energy_bound"),
                H("Actual density supplies the original coefficient energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N>=3 and real a,b with N<=a<=b, use the same "
                        + "literal partial-cell masses, full-block Gram and original coefficients A_m. "
                        + "Then sum_(N<=m<2N) A_m^2/w(m) <= (1+1/log(N))^2/(8*N). "
                        + "The coefficient A already contains the factor log(N). Equal endpoints "
                        + "are included. The endpoint b needs no upper bound: every original "
                        + "cell integral is clipped to its own unit cell.")),
                    Paragraph(Text(
                        "Write B=1+1/log(N). On each original unit cell, "
                        + "k(t)=[1/log(t)+1/log(t)^2]/t^2 is bounded by "
                        + "[1/log(N)+1/log(N)^2]/t^2. The exact integral of 1/t^2 "
                        + "over [m,m+1] is w(m). Positivity of the clipped density therefore "
                        + "gives 0<=d_m<=B for the original datum d_m=log(N)*omega_m/w(m). "
                        + "The two exact moments eliminate the cross terms in the weighted "
                        + "least-squares expansion about the constant B/2. Hence the residual "
                        + "energy is at most sum w(m)*(d_m-B/2)^2, which is at most "
                        + "B^2/4 times the weight mass sum w(m)=1/(2*N), giving B^2/(8*N). Both original Cramer coordinates "
                        + "and their mixed correction remain in that expansion.")),
                    Paragraph(Text(
                        "This supplies a finite upper bound from the actual density rather than "
                        + "assuming an energy allowance. It does not prove a sharp finite endpoint "
                        + "maximizer, a signed residual estimate, an analytic Mobius-prefix rate, "
                        + "the complete cutoff payments, strict Robin above 5040 or RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-partial-cell-response-projection-interface"),
                DeclarationHandle.Create(Prefix + "response_projection_interface"),
                H("Exact public interface to the unchanged original projection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N>=3, on S(N)={m in N:N<=m<2N}, "
                        + "the exact original Gram entries satisfy G00=sum w(m), "
                        + "G01=sum w(m)*m/N, G10=G01, and G11=sum w(m)*(m/N)^2; "
                        + "the original determinant Delta(N)>0. For every real a,b, "
                        + "sum A(N,a,b,m)=0 and sum m*A(N,a,b,m)=0. "
                        + "For every real a,b and every natural m in S(N), "
                        + "A(N,a,b,m)=log(N)*omega(a,b,m)-c0*w(m)-c1*[w(m)*m/N]. "
                        + "There are no endpoint order, strictness or upper-bound hypotheses "
                        + "on a,b in this interface.")),
                    Paragraph(Text(
                        "This single additive theorem binds the original private Gram-entry, "
                        + "positive-determinant, exact-moment and on-block coefficient proofs "
                        + "directly. The separate response-adjoint module is its actual consumer. "
                        + "No original definition, proof, accepted energy content or owner import "
                        + "is replaced. It makes no interval-sign, cofinal or RH assertion. "
                        + "This interface and its Reg/Scribe additions have completed local scoped "
                        + "validation; repository PR and CI acceptance remain separate delivery steps."))),
                DescribeRole.Theorem))));
}
