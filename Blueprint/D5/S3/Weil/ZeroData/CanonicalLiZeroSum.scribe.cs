using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class CanonicalLiZeroSumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZeroData/CanonicalLiZeroSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/lagarias2004li");
    private static Formula K => F.Id("k");
    private static Formula N => F.Id("n");
    private static Formula Rho => Seq(F.Id("rho"), Open, F.Id("Z"), Comma, K, Close);
    private static Formula Mass => Seq(F.Id("m"), Open, F.Id("Z"), Comma, K, Close);
    private static Formula Li => Seq(F.Id("lambda"), Underscore, Grp(N));
    private static Formula Statement => Seq(
        Forall, Sp, F.Id("Z"), InMacro, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
        Forall, Sp, N, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Li, Eq, Sum, Underscore, Grp(K, Eq, D(0)), Caret, Grp(Infty), Sp,
        Mass, Open, D(1), Minus, Re, Open, Open, D(1), Minus,
        Frac, Grp(D(1)), Grp(Rho), Close, Caret, Grp(N), Close, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The derivative-defined Li coefficients are the absolutely convergent real sums "
            + "over all actual nontrivial zeta zeros.",
        H("Canonical Li Coefficients as Actual Zero Sums"),
        Blocks(
            Paragraph(Text(
                "Let Z be any exhaustive, injective enumeration of the actual nontrivial "
                    + "zeros of the Riemann zeta function with exact analytic multiplicities. "
                    + "Write rho(Z,k)=rho_k=Z.zero(k), m(Z,k)=m_k=Z.multiplicity(k), and "
                    + "gamma_k=-i*(rho_k-1/2). The symbol lambda_n denotes the existing "
                    + "canonicalLiCoefficient n, defined by derivatives of the logarithm "
                    + "of the completed xi function. The index n ranges over all natural "
                    + "numbers, including zero.")),
            Describe.Lean(
                DescribeId.Create("canonical-li-real-zero-sum"),
                DeclarationHandle.Create(Owner + "canonical_li_eq_zero_real_sum"),
                H("Unconditional identification for every degree"),
                StatementSource.FromAuthor(Disp(Statement)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The real series on the right is absolutely summable by "
                            + "li_zero_real_summable. No Riemann hypothesis, half-plane "
                            + "nonvanishing premise, or numerical lower bound for zero "
                            + "heights is required.")),
                    Paragraph(Text(
                        "Put L=xi'/xi and s=(1-z)^(-1). Subtracting the normalized xi "
                            + "resolvents at s and 1-s cancels the constant at zero. "
                            + "The reflection identity L(1-s)=-L(s) then expresses "
                            + "G(z)=(1-z)^(-2)L(s) as the sum of the kernels "
                            + "Phi_k(z)=m_k/2*(2/(1-z)-q_k/(1-q_k*z)-r_k/(1-r_k*z)), "
                            + "where q_k=1-1/rho_k and r_k=1-1/(1-rho_k).")),
                    Paragraph(Text(
                        "For D_k=rho_k*(1-rho_k)=gamma_k^2+1/4 and x_k=1/D_k, "
                            + "the identities q_k*r_k=1 and q_k+r_k=2-x_k collapse "
                            + "the rational kernel to "
                            + "Phi_k(z)=m_k/2*x_k*(1+z)/((1-z)*((1-z)^2+x_k*z)). "
                            + "For |gamma_k|>=2, one has |x_k|<=1/2 and "
                            + "|x_k|<=2/(1+|gamma_k|^2). On |z|<=1/4, the two "
                            + "denominator factors have norms at least 3/4 and 7/16. "
                            + "Consequently |Phi_k(z)|<=4*m_k/(1+|gamma_k|^2). "
                            + "This majorant is summable; the remaining zero indices "
                            + "form a finite set.")),
                    Paragraph(Text(
                        "Since xi(1)=1/2, a sufficiently small ball about zero contains "
                            + "no pole of any kernel. The cofinite majorant gives uniform "
                            + "convergence there, and holomorphic differentiation gives "
                            + "convergence of every derivative over all finite subsets "
                            + "of the zero indices. The d-th derivative at zero divided "
                            + "by d! of an individual kernel is "
                            + "m_k/2*(2-q_k^(d+1)-r_k^(d+1)). "
                            + "The existing generator_taylor_coefficient identifies "
                            + "the derivative of G with lambda_(d+1).")),
                    Paragraph(Text(
                        "Taking real parts yields the average of the original real Li "
                            + "summand and its reflected summand. The stored permutation "
                            + "rho -> 1-rho preserves multiplicities, so absolute real "
                            + "summability makes the two sums equal. This proves the "
                            + "displayed identity for positive n; both sides vanish at "
                            + "n=0. No absolute convergence of the unpaired complex "
                            + "Li summands is asserted."))),
                DescribeRole.Theorem))));
}
