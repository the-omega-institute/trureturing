using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PentagonQuarticTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/PentagonQuarticTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit quartic sum of squares gives the sharp coefficient eight for Hermitian matrices with pentagon support.",
        H("The Hermitian pentagon quartic certificate"),
        Blocks(
            Entry("pentagon-quartic-sos", "pentagon_quartic_sos", "The exact trace certificate", General(Sos()),
                "Let n be any finite type with decidable equality and let A(i) be arbitrary complex matrices on n, for i in Fin 5. All index additions are modulo five. Assume that every A(i) is Hermitian and A(i)A(i+2)=0. Write ReTr for the real part of the ordinary, unnormalized trace and hsSq(B)=ReTr(B adjoint B). Set F(i)=A(i+4)+A(i+1), R(i)=A(i)^2-(A(i)F(i)+F(i)A(i))/2, and C(i)=A(i)A(i+1)-A(i+1)A(i). The identity and the five aggregation identities are attributed to the supplied mathematical source pentagon-quartic-joint-source/proof.txt, SHA-256 83ef9890d59944d8f6789d3e73dff4695ab3999c76d3e9b440eed74b40812280. No positive-semidefinite hypothesis is used.",
                "To see the coefficients, write T=sum ReTr(A(i)^4), U31=sum ReTr(A(i)^3 A(i+1)+A(i)A(i+1)^3), U22=sum ReTr(A(i)^2 A(i+1)^2), Ualt=sum ReTr(A(i)A(i+1)A(i)A(i+1)), and Ustar=sum ReTr(A(i+4)A(i)A(i+1)A(i)). Cyclic trace and the forbidden products give ReTr(S^4)=T+4U31+4U22+2Ualt+4Ustar. For the real Hilbert--Schmidt pairing, the remainder correlations at distances zero, one and two are T-2U31+U22+Ualt+Ustar, -U31+3U22/2+Ualt/2+Ustar, and Ustar/2. The commutator correlations at distances zero and one are 2U22-2Ualt and 2Ustar. The cyclic quadratic forms combine these as 7r0-10r1+3r2+2c0-5c1/4, exactly 8T-ReTr(S^4)."),
            Entry("pentagon-quartic-bound", "pentagon_quartic_trace_le", "The quartic trace bound", General(Bound()),
                "Every Hilbert--Schmidt square is nonnegative, since B adjoint B is positive semidefinite. The four coefficients 1, 1/2, 3/4 and 5/8 are positive, so the certificate gives the dimension-independent inequality. The empty finite type is included. No rank restriction, projection reduction, real-entry assumption, invertibility or simultaneous diagonalization is used.",
                "The supplied analytic positive Schatten duality argument at the conjugate exponents 4 and 4/3 converts this bound into sum Tr((P(i) X P(i))^(4/3)) <= 2 Tr(X^(4/3)) for X positive semidefinite and projections with P(i)P(i+2)=0. The primary source arXiv:2610.20775v1, Section 3.1, equation (11), uses the graph normalization 1/theta_alpha=sup min_i Z_(1-alpha). With this normalization, substituting X=sigma^(3/4) gives theta_(1/4)(C5)=5/2. The primary Proposition 3.3(ii) and flat witness then give the plateau [1/4,2]. These Schatten and graph consequences are analytic only here; this module proves the integer quartic matrix statements. This is the quartic consequence; higher-degree analytic plateau improvements are outside this module. The full curve remains open, and no literature priority is asserted."),
            Entry("pentagon-quartic-sharp", "constant_eight_sharp", "Every smaller coefficient fails", Sharp(),
                "For every real c<8, the strict reverse inequality occurs already on the one-dimensional complex space. Take A(0)=A(1)=1 and all other A(i)=0. The five support relations and Hermiticity hold, sum ReTr(A(i)^4)=2, and ReTr((sum A(i))^4)=16. Thus c times the former is strictly less than the latter. This proves optimality of eight for the same universal Hermitian inequality.",
                "An additional analytic equality example uses the five diagonal projections onto span(e(i),e(i+1)) in dimension five. Their sum is 2I, T=10 and Tr(S^4)=80; all R(i) and C(i) vanish. The one-dimensional witness in the displayed theorem suffices to establish sharpness."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement,
        string description, string proof) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description)), Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string s) => F.Id(s);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin5() => Call("Fin", D(5));
    private static Formula Matrix(Formula n) => Call("Matrix", n, n, Complex());
    private static Formula All(string x, Formula t, Formula p) =>
        Seq(Forall, Sp, V(x), Colon, Sp, t, Comma, Sp, p);
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula At(string f, Formula x) => App(V(f), x);
    private static Formula Shift(int k) => k == 0 ? V("i") : Add(V("i"), D((byte)k));
    private static Formula A(int k = 0) => At("A", Shift(k));
    private static Formula R(int k = 0) => At("R", Shift(k));
    private static Formula C(int k = 0) => At("C", Shift(k));
    private static Formula Sum(Formula x) => Seq(F.Sum, Underscore, Grp(V("i"), Colon, Fin5()), Sp, x);
    private static Formula Tr(Formula x) => Call("ReTr", x);
    private static Formula Hs(Formula x) => Call("hsSq", x);
    private static Formula Pow(Formula x, byte p) => new Formula.Power(Seq(Open, x, Close), D(p));
    private static Formula Frac(byte a, byte b) => new Formula.Fraction(D(a), D(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Assumptions() => And(
        Seq(Open, All("i", Fin5(), Call("IsHermitian", A())), Close),
        Seq(Open, All("i", Fin5(), Eq(Mul(A(), A(2)), D(0))), Close));
    private static Formula T() => Sum(Tr(Pow(A(), 4)));
    private static Formula S4() => Tr(Pow(Sum(A()), 4));
    private static Formula Bound() => Le(S4(), Mul(D(8), T()));
    private static Formula Sos() => Eq(Sub(Mul(D(8), T()), S4()),
        Add(Add(Add(Sum(Hs(Sub(R(), R(1)))),
            Mul(Frac(1, 2), Sum(Hs(Sub(Add(Sub(R(), Mul(D(2), R(1))), Mul(D(2), R(2))), R(3)))))),
            Mul(Frac(3, 4), Sum(Hs(C())))),
            Mul(Frac(5, 8), Sum(Hs(Sub(C(), C(1)))))));
    private static Formula General(Formula p) => All("n", V("Type"),
        Seq(OpenBracket, Call("Fintype", V("n")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", V("n")), CloseBracket, Sp,
            All("A", Seq(Fin5(), To, Sp, Matrix(V("n"))), Imp(Assumptions(), p))));
    private static Formula Sharp() => All("c", Real(), Imp(Lt(V("c"), D(8)),
        Seq(Exists, Sp, V("A"), Colon, Sp, Fin5(), To, Sp, Matrix(Call("Fin", D(1))), Comma, Sp,
            And(Assumptions(), Lt(Mul(V("c"), T()), S4())))));
}
