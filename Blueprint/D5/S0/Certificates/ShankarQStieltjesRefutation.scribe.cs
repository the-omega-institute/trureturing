using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class ShankarQStieltjesRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/ShankarQStieltjesRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/shankar2026canon");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula T => F.Id("t");
    private static Formula K => F.Id("k");
    private static Formula Q(Formula k) => Call("closedFormQ", k);
    private static Formula C(Formula i) => Call("certificate", i);
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Index(Formula s) => Add(Add(I, J), s);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula SumOver(Formula v, Formula n, Formula f) =>
        Seq(Sum, Underscore, Grp(v, Colon, Fin(n)), f);
    private static Formula RangeSum(Formula v, Formula lo, Formula hi, Formula f) =>
        Seq(Sum, Underscore, Grp(v, Eq, lo), Caret, Grp(hi), f);
    private static Formula Binom(Formula m, Formula j) => Call("binom", m, j);
    private static Formula Integral(Formula n) =>
        Seq(F.Int, Underscore, Grp(R), Pow(T, n), Thin, F.Id("d"), Mu, Open, T, Close);
    private static Formula Support() => Call("AE", Mu, Seq(T, Mapsto, Sp, D(0), Leq, Sp, T));
    private static Formula Moments() => Seq(Forall, Sp, F.Id("a"), InMacro, Sp, N, Comma,
        Call("Integrable", Seq(T, Mapsto, Sp, Pow(T, F.Id("a"))), Mu));
    private static Formula BigInteger(string digits) =>
        D(digits.Select(static digit => (byte)(digit - '0')).ToArray());
    private static Formula NegativeValue() => Seq(Minus,
        BigInteger("7376954157543403276318358565675383034355744240767681002284188705571519096491185"));
    private static Formula Quadratic() => SumOver(I, D(1, 1), SumOver(J, D(1, 1),
        Seq(C(I), Cdot, C(J), Cdot, Q(Index(D(3))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact degree-ten polynomial certificate excludes every positive measure with "
            + "finite moments on the nonnegative half-line for Shankar's Q closed form.",
        H("Shankar Q Stieltjes Refutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("shankar-source-closed-form"),
                DeclarationHandle.Create(Prefix + "closedFormQ"),
                H("The published closed form"), StatementSource.FromAuthor(SourceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "closedFormQ maps natural numbers to integers. All summation bounds are "
                    + "inclusive. binom(m,j) is zero for j negative "
                    + "or greater than m, and is the ordinary binomial coefficient otherwise. "
                    + "Subtraction in the lower indices is integer subtraction, so the b=1 "
                    + "term has E(r,1)=1. The b-sum is empty when k=1. The Lean definition "
                    + "uses Mathlib's catalan; catalan_eq_centralBinom_div and "
                    + "succ_mul_catalan_eq_centralBinom justify the displayed Catalan fraction.")),
                    Paragraph(Text(
                    "Shankar, arXiv:2608.30002v2, Theorem 7.1 identifies this formula with "
                    + "the number of 321-avoiding lattice words containing k copies of each "
                    + "of 1,2,3. That source-to-count identification is a published input, "
                    + "not a Lean theorem or axiom here. The kernel statements below concern "
                    + "the displayed closed form. Conjecture 9.5 also mentions B, which this "
                    + "result does not settle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shankar-exact-certificate"),
                DeclarationHandle.Create(Prefix + "certificate"),
                H("Integer polynomial coefficients"), StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The domain is Fin(11) and the codomain is the integers. Coefficients "
                    + "are listed in ascending degree: p(t) is the sum of certificate(i) "
                    + "times t to the power i. Exact rational elimination produced this "
                    + "primitive integer witness. No floating-point value is used in Lean."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shankar-certificate-exact-value"),
                DeclarationHandle.Create(Prefix + "certificate_value"),
                H("Exact negative quadratic form"),
                StatementSource.FromAuthor(Disp(Seq(Quadratic(), Eq, NegativeValue()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Kernel reduction verifies all needed closed-form values before checking "
                    + "the integer quadratic form. The private checked-value vector is proved "
                    + "equal to the formula on Fin(24); it does not define the sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shankar-certificate-negative"),
                DeclarationHandle.Create(Prefix + "certificate_negative"),
                H("Strict negativity"),
                StatementSource.FromAuthor(Disp(Seq(Quadratic(), Lt, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The strict sign follows from the checked integer value and is used "
                    + "in the no-representation theorem."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("stieltjes-moment-quadratic-nonnegative"),
                DeclarationHandle.Create(Prefix + "moment_quadratic_nonnegative"),
                H("Positive measures give nonnegative shifted forms"),
                StatementSource.FromAuthor(PositivityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Measure(R) denotes positive Borel measures. AE(mu,t maps to P(t)) "
                    + "means P holds mu-almost everywhere. Each monomial is integrable. "
                    + "Constant multiplication and finite sums therefore justify moving "
                    + "both sums through the integral. Expanding the square identifies the "
                    + "form with the integral of t^s times the square of the finite polynomial; "
                    + "the integrand is nonnegative on the support."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("shankar-closed-form-not-stieltjes"),
                DeclarationHandle.Create(Prefix + "closed_form_not_stieltjes"),
                H("No Stieltjes representation of the closed form"),
                StatementSource.FromAuthor(RefutationFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The theorem has no assumed sequence values or positivity hypotheses: "
                    + "it denies the existence of a measure satisfying all three displayed "
                    + "conditions. Specializing the preceding positivity lemma to n=11, s=3, "
                    + "and the real casts of the integer certificate contradicts strict "
                    + "negativity. Through published Theorem 7.1 this refutes the Q clause "
                    + "of Conjecture 9.5. A bounded later-literature search found no settlement; "
                    + "novelty remains suspected and independent source review is required."))),
                DescribeRole.Theorem))));

    private static Formula SourceFormula()
    {
        Formula b = F.Id("b"), c = F.Id("c"), r = F.Id("r");
        Formula upperH = Sub(Sub(Seq(D(2), K), b), c);
        Formula h = Seq(Open, Binom(upperH, Sub(K, b)), Minus,
            Binom(upperH, Sub(Sub(K, b), D(1))), Close);
        Formula upperE = Sub(Add(r, b), D(1));
        Formula e = Seq(Open, Binom(upperE, Sub(b, D(1))), Minus,
            Binom(upperE, Sub(b, D(2))), Close);
        Formula inner = RangeSum(r, b, Sub(K, D(1)), Seq(e, Cdot,
            Binom(Add(Sub(Sub(K, D(1)), r), c), c)));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Q(D(0)), Eq, D(1), Comma, RowBreak, Grp(),
            Forall, Sp, K, InMacro, Sp, N, Comma, D(1), Leq, Sp, K,
            Rightarrow, RowBreak, Grp(),
            Q(K), Eq, Frac, Grp(Binom(Seq(D(2), K), K)), Grp(Add(K, D(1))), Plus,
            RangeSum(b, D(1), Sub(K, D(1)), RangeSum(c, D(0), b, Seq(h, Cdot, inner))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CertificateFormula()
    {
        string[] values = [
            "101118710150832431671196796252649512231806",
            "-662677669268533938101716987475663620965666",
            "1548486277071801438600832338542573144101640",
            "-1800082554673557385076101398989780036003293",
            "1196307300703816610151657807611194412954834",
            "-487410702796750216586043273691945221737851",
            "125698717484820716392581080465507901682426",
            "-20562809439083017274073234871446233006372",
            "2065883321354005872852404249559173330738",
            "-116172686339782400824354774056669210149",
            "2797672051379430758385367063062351871"];
        Formula[] rows = values.Select((value, index) => Seq(
            index == 0 ? Seq() : Seq(RowBreak, Grp()),
            C(BigInteger(index.ToString(System.Globalization.CultureInfo.InvariantCulture))), Eq,
            value.StartsWith('-') ? Seq(Minus, BigInteger(value[1..])) : BigInteger(value))).ToArray();
        return Disp(Seq(Begin, Grp(F.Id("gathered")), Seq(rows), End, Grp(F.Id("gathered"))));
    }

    private static Formula PositivityFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), d = F.Id("d");
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, Mu, Colon, Call("Measure", R), Comma,
            Open, Open, Support(), Close, Land, Open, Moments(), Close, Close,
            Rightarrow, RowBreak, Grp(), Forall, Sp, n, Comma, s, InMacro, Sp, N, Comma,
            Forall, Sp, d, Colon, Fin(n), To, Sp, R, Comma, RowBreak, Grp(),
            D(0), Leq, SumOver(I, n, SumOver(J, n,
                Seq(Call("d", I), Cdot, Call("d", J), Cdot, Integral(Index(s))))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula RefutationFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Neg, Sp, Exists, Sp, Mu, Colon, Call("Measure", R), Comma,
        Open, Support(), Close, Land, RowBreak, Grp(), Open, Moments(), Close, Land,
        RowBreak, Grp(), Open, Forall, Sp, F.Id("n"), InMacro, Sp, N, Comma,
        Integral(F.Id("n")), Eq, Q(F.Id("n")), Close, End, Grp(F.Id("gathered"))));
}
