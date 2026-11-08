using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PentagonQuinticTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/PentagonQuinticTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven explicit rational PSD-weighted squares give the sharp fifth-moment coefficient sixteen on the pentagon.",
        H("The complex PSD pentagon fifth moment"),
        Blocks(
            Entry("pentagon-quintic-sos", "pentagon_quintic_sos", "The exact seven-square identity", General(Sos(), false),
                "Let n be any finite type with decidable equality and A(i) complex matrices on n indexed by Fin 5. Index additions are modulo five. For this identity assume Hermiticity and A(i)A(i+2)=0. ReTr denotes the real part of the ordinary trace and weightedSquare(a,B)=ReTr(B adjoint a B). Put L=A(i-1)A(i-2), M=A(i+1)A(i+2), Dminus=A(i-1)^2-A(i-1)A(i), Dplus=A(i+1)^2-A(i+1)A(i), Fminus=A(i-1)^2-A(i)A(i-1), Fplus=A(i+1)^2-A(i)A(i+1), H=A(i)^2-A(i-1)^2-A(i+1)^2. The ordered even vector is E=(L+M,Dminus+Dplus,Fminus+Fplus,H) and the odd vector is O=(L-M,Dminus-Dplus,Fminus-Fplus). The identity is attributed to the supplied mathematical source pentagon-quintic-joint-source/proof.txt, SHA-256 9ecd6884c7788722176850d88a786d0306243f9373e333ed25ff6b557faf101a.",
                "The seven B entries are E0-E1+7E2/8+3E3/2, E1+E2/6+7E3/6, E2+316E3/325, E3, O0-O1/3+O2/6, O1-O2/2, O2. Their weights w are 2,3,325/96,4181/1300,3,2/3,1/4. Sixteen separately proved Gram entries and five bounded first-factor expansions establish the exact ordered trace identity. The two oriented five-cycle words occur with their actual order. Cyclicity preserves each orientation; adjoint reversal conjugates the complex trace, and a separate lemma identifies their real parts. No complex trace is assumed to equal its reverse, and no cycle term is assigned a sign."),
            Entry("pentagon-quintic-bound", "pentagon_quintic_trace_le", "The universal PSD bound", General(Bound(), true),
                "Assume every A(i) is positive semidefinite and A(i)A(i+2)=0. PSD congruence gives B adjoint A(i) B positive semidefinite for every complex B. Its real trace is nonnegative. All seven rational weights are strictly positive, so the exact identity proves the inequality in every finite dimension, including the empty dimension. Singular and zero matrices are included. Positivity is used here; no corresponding Hermitian fifth-moment inequality is asserted. There is no reality, commutativity, rank, repeated-spectrum or invertibility restriction.",
                "The analytical positive Schatten duality uses p=5/4 and q=5. For projections P(i) with P(i)P(i+2)=0 and X positive semidefinite, let Y(i)=P(i)XP(i) and L=sum Tr(Y(i)^(5/4)). For L>0 set C(i)=Y(i)^(1/4)/L^(1/5). These are PSD, supported in P(i), and sum Tr(C(i)^5)=1. Holder and the fifth-moment inequality give L^(4/5)<=16^(1/5) Tr(X^(5/4))^(4/5), hence L<=2 Tr(X^(5/4)); the zero case is immediate. In the primary projection formula, X=sigma^(4/5) gives min_i Z_(4/5)<=2/5 and theta_(1/5)(C5)>=5/2. The flat faithful witness sigma=I/5 attains equality, and primary monotonicity supplies [1/5,2]. These fractional-power, duality and graph statements are analytical here. The stronger analytical sixth-degree plateau [1/6,2] is outside this Lean module. The full curve remains open and no literature priority is certified. The primary definitions, original [1/2,2] plateau and umbrella with optimized centers are attributed to Mghirbi and Douglas, arXiv:2610.20775v1; see Library/Entropy/mghirbi2026renyi.md."),
            Entry("pentagon-quintic-sharp", "constant_sixteen_sharp", "The constant sixteen is sharp", Sharp(),
                "For every real c<16 choose scalar complex PSD matrices A(0)=A(1)=1 and A(2)=A(3)=A(4)=0. All five support relations hold, sum ReTr(A(i)^5)=2 and ReTr((sum A(i))^5)=32. Thus the bound with c fails already in dimension one, for the same PSD domain.",
                "The additional analytical flat example consists of five diagonal projections onto span(e(i),e(i+1)) in dimension five. Its sum is 2I, total fifth moment is 10 and the sum's fifth moment is 160. The scalar example already proves the formal optimality statement; the full flat projection and fractional-power consequences are outside its compiled scope."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement,
        string description, string proof) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mghirbi2026renyi")),
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
    private static Formula Sum(Formula x) => Seq(F.Sum, Underscore, Grp(V("i"), Colon, Fin5()), Sp, x);
    private static Formula Tr(Formula x) => Call("ReTr", x);
    private static Formula Pow(Formula x, byte p) => new Formula.Power(Seq(Open, x, Close), D(p));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Assumptions(bool psd) => And(
        Seq(Open, All("i", Fin5(), Call(psd ? "PosSemidef" : "IsHermitian", A())), Close),
        Seq(Open, All("i", Fin5(), Eq(Mul(A(), A(2)), D(0))), Close));
    private static Formula T() => Sum(Tr(Pow(A(), 5)));
    private static Formula S5() => Tr(Pow(Sum(A()), 5));
    private static Formula Bound() => Le(S5(), Mul(D(16), T()));
    private static Formula Sos() => Eq(Sub(Mul(D(16), T()), S5()),
        Sum(Seq(F.Sum, Underscore, Grp(V("k"), Colon, Call("Fin", D(7))), Sp,
            Mul(At("w", V("k")), Call("weightedSquare", A(), Call("B", V("i"), V("k"))))));
    private static Formula General(Formula p, bool psd) => All("n", V("Type"),
        Seq(OpenBracket, Call("Fintype", V("n")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", V("n")), CloseBracket, Sp,
            All("A", Seq(Fin5(), To, Sp, Matrix(V("n"))), Imp(Assumptions(psd), p))));
    private static Formula Sharp() => All("c", Real(), Imp(Lt(V("c"), D(16)),
        Seq(Exists, Sp, V("A"), Colon, Sp, Fin5(), To, Sp, Matrix(Call("Fin", D(1))), Comma, Sp,
            And(Assumptions(true), Lt(Mul(V("c"), T()), S5())))));
}
