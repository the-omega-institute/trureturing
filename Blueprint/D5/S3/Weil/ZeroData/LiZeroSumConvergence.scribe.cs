using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class LiZeroSumConvergenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZeroData/LiZeroSumConvergence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/lagarias2004li");
    private static Formula K => F.Id("k");
    private static Formula N => F.Id("n");
    private static Formula T => F.Id("T");
    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);
    private static Formula Rho => Seq(F.Id("rho"), Underscore, Grp(K));
    private static Formula Multiplicity => Seq(F.Id("m"), Underscore, Grp(K));
    private static Formula Power => Seq(Open, D(1), Minus, Frac, Grp(D(1)), Grp(Rho),
        Close, Caret, Grp(N));
    private static Formula RealTerm => Seq(Multiplicity, Open, D(1), Minus, Re,
        Open, Power, Close, Close);
    private static Formula ComplexTerm => Seq(Multiplicity, Open, D(1), Minus, Power, Close);
    private static Formula RealSum => Seq(Sum, Underscore, Grp(K, Eq, D(0)),
        Caret, Grp(Infty), Sp, RealTerm);
    private static Formula Quantified(Formula statement) => Seq(
        Forall, Sp, F.Id("Z"), InMacro, Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
        Forall, Sp, N, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp, statement);
    private static Formula Limit(string cutoff) => Call("Tendsto", Seq(
        Open, T, Mapsto, Sum, Underscore, Grp(K, InMacro, Call(cutoff, T)), Sp,
        ComplexTerm, Close, Comma, Sp, F.Id("atTop"), Comma, Sp,
        Call("nhds", RealSum)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real Li series over actual zeta zeros is absolutely summable, and three "
            + "conjugate-paired cutoff sums converge to its real value.",
        H("Li Zero-Sum Convergence"),
        Blocks(
            Paragraph(Text(
                "Z is any exhaustive, injective enumeration of the actual nontrivial zeros "
                    + "of the Riemann zeta function, with exact positive analytic multiplicities. "
                    + "In particular, the existing zetaZeroData in UnconditionalCanonicalZeroData "
                    + "is a canonical instance. The natural index n includes zero. Set "
                    + "rho_k=Z.zero(k), m_k=Z.multiplicity(k), and gamma_k=-i*(rho_k-1/2). "
                    + "The strict strip 0<Re(rho_k)<1 is part of the actual-zero data.")),
            Describe.Lean(
                DescribeId.Create("real-li-summability"),
                DeclarationHandle.Create(Owner + "li_zero_real_summable"),
                H("Absolute summability of the real parts"),
                StatementSource.FromAuthor(Disp(Quantified(
                    Call("Summable", Seq(K, Mapsto, Sp, RealTerm))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The summand is m_k*(1-Re((1-1/rho_k)^n)). For |gamma_k|>=2 its "
                        + "absolute value is at most 4*2^n*m_k/(1+|gamma_k|^2). "
                        + "First-order real-part cancellation supplies the inverse-square decay: "
                        + "for u=1/rho_k, |Re(u)|<=|u|^2, and a power induction bounds "
                        + "|1-Re((1-u)^n)| by (2^n-1)*|u|^2. The existing reciprocal-square "
                        + "zeta-weight theorem makes this majorant summable. All remaining "
                        + "low-zero terms form a finite set and are retained. The factor 4*2^n "
                        + "is a convergence majorant, not a value of the first Li coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-li-cutoff-limits"),
                DeclarationHandle.Create(Owner + "li_zero_cutoff_limits"),
                H("Spectral, height, and radial cutoffs have the same limit"),
                StatementSource.FromAuthor(Disp(Quantified(Seq(
                    Limit("Sgamma"), Land, Sp, Limit("Sheight"), Land, Sp, Limit("Sradial"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every finite summand is m_k*(1-(1-1/rho_k)^n). The three index sets "
                        + "contain exactly the zeros satisfying |gamma_k|<=T, |Im(rho_k)|<=T, "
                        + "and |rho_k|<=T, respectively; these are Sgamma(T), Sheight(T), "
                        + "and Sradial(T) in the formula. T is real, atTop means T tends to "
                        + "positive infinity, and nhds is the complex neighborhood filter "
                        + "of the displayed real sum cast into C. The latter two sets are filters of the "
                        + "spectral ball at T+1; their membership equalities hold for all real T, "
                        + "including nonpositive cutoffs. Each set is invariant under complex "
                        + "conjugation and eventually contains every finite set of indices. "
                        + "Finite conjugate pairing makes each complex sum the cast of its "
                        + "real-part sum. Absolute real summability then gives the three limits. "
                        + "Lagarias equation (1.1) uses the radial convention; Suzuki equation "
                        + "(1.1) uses the height convention, as detailed in the source note."))),
                DescribeRole.Theorem),
            Describe.Remark(
                DescribeId.Create("presentation-and-identity-boundary"),
                DeclarationHandle.Create(Owner + "li_zero_cutoff_limits"),
                H("Presentation independence and the derivative identity"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing zeroEquiv transports the absolutely summable real series "
                        + "between any two actual-zero presentations; the exact multiplicities "
                        + "are identified by multiplicity_eq_zeroMult. No second Li sequence "
                        + "is defined. Identifying this common limit with the canonical "
                        + "derivative coefficient remains a separate open identity. These "
                        + "theorems assume no Riemann hypothesis, representation formula, or "
                        + "convergence premise, and assert no absolute summability of the "
                        + "unpaired complex terms.")))))));
}
