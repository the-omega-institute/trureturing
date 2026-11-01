using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OneSidedGoldenHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete retained golden histories.", H("Complete retained golden histories"), Blocks(
            Describe.Lean(DescribeId.Create("native-predictor-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OneSidedGoldenHistory.native_predictor_minimum"),
                H("Complete retained golden histories"), StatementSource.FromAuthor(Disp(NativeFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be any Hermitian idempotent on a finite complex matrix carrier and let E=I-P. The task predicts the next outcome under repeated use of this fixed instrument; it does not recover complete histories, quantum states or responses under other gates. The initial state is an arbitrary density matrix, including coherent off-diagonal blocks. Put q=Re Tr(P rho), and assume 0<q<1. In the displayed formula, ofMatrixInverse(val(r)) is the raw matrix CStarMatrix.ofMatrix.symm r.val; card is Fintype.card, Sum is the disjoint sum, and contains is list membership.")),
                    Paragraph(Text("Set x=1/phi, where phi=(1+sqrt(5))/2, and retain the relative phase zeta^(-3), where zeta=exp(3 pi i/5). The two Kraus branches are M0=sqrt(x) E and M1=x E+zeta^(-3) P. Their adjoint products sum to the identity. Branch states are M_i rho M_i*, and every outcome is retained in source order through runWord.")),
                    Paragraph(Text("The mass of every finite Boolean history is the real trace of its branch state and is strictly positive. For n consecutive one outcomes the mass equals q+(1-q)x^(2n), and the conditional P weight is q divided by this mass. The next-zero probability is the ratio of the extended-history mass to the history mass.")),
                    Paragraph(Text("After any zero, the posterior P weight is zero and the conditional next-zero probability is x. At every all-one history of length n, including n=0, it is x(1-q)x^(2n)/(q+(1-q)x^(2n)). The computation keeps both CP branches and their relative phase; it does not replace the instrument by a supplied scalar-law certificate.")),
                    Paragraph(Text("For every 0 < epsilon < x/2 there is a first nonstrict cutoff N with p(n) <= 2 epsilon exactly when N <= n. A total predictor on Fin(N+1)+Unit attains N+2 states, and every correct predictor on every finite carrier has at least this many states. This includes N=0 and threshold equality. Correctness is tested on the actual conditional trace probabilities at every positive history; it does not assume the scalar law.")),
                    Paragraph(Text("For epsilon >= x/2 a single state outputting x/2 suffices. At epsilon=0 no finite predictor is correct, because the positive age probabilities tend to zero and a finite total-update orbit must repeat. Only the state count is asserted. The natural ceiling definition of N is the ceiling of log((1-q)(x-2 epsilon)/(2 epsilon q))/(2 log phi), truncated at zero; Nat.ceil_le gives the nonstrict threshold, including integer ties. The following asymptotic and supplied-clock consequences are applications of this theorem and the cited pinned library results; they add no separate mathematical declaration.")),
                    Paragraph(Text("For fixed q in (0,1), put L(epsilon)=log(1/epsilon), D=2 log phi and A(epsilon)=(1-q)(x-2 epsilon)/(2q). As epsilon tends to zero from above, A tends to the positive number (1-q)x/(2q), L tends to infinity, and the real argument f of the natural ceiling equals (L+log A)/D. Thus f/L tends to 1/D. The pinned Mathlib limit tendsto_nat_ceil_div_atTop gives ceil(f)/f tending to one. Consequently (N+2)/L tends to 1/D, which yields O(log(1/epsilon)) states. The constants depend on the fixed q; this is not a uniform q-endpoint estimate.")),
                    Paragraph(Text("For m=N+2 let B=Nat.clog 2 m. The pinned Mathlib identity Real.natCeil_logb_natCast gives B=ceil(log(m)/log(2)). The positive state-ratio limit implies log(m)/log(L) tends to one. Applying the same ceiling limit gives B/log(L) tending to 1/log(2), hence O(log log(1/epsilon)) encoding bits. Function.Embedding.nonempty_iff_card_le and Nat.le_pow_clog supply an actual injection of Fin(N+1)+Unit into functions from Fin(B) to Bool. This counts state labels; it provides no bound on output installation, numerical precision, computation time, instrument construction or archive size.")),
                    Paragraph(Text("With a separately supplied exact depth, define the flag of a history as its Boolean any-test for an outcome zero. The initial flag is false and the total update is oldFlag OR (currentOutcome=zero). List.any_append verifies this update at every history. Reading x when the flag is true and ageProbability(q,n) otherwise equals the actual conditional trace probability for every finite history, by native_predictor_minimum. Both outputs are in [0,1]. The flag has two states, while the complete depth-and-flag carrier is Nat times Bool and is infinite; depth increments on each outcome. This augmented readout receives n as an additional argument. Its unbounded clock is a supplied resource, and the finite fully charged predictor lower bound still applies to the original contract.")),
                    Paragraph(Text("The degenerate q endpoints are context outside the fixed-q theorem and its asymptotic application. The explicit retained Born/CP interpretation remains the model premise; neither the asymptotic application nor the augmented clock construction establishes calibration or physical clock acquisition.")),
                    Paragraph(Text("The explicit Born/CP retained-readout interpretation is a model premise. The preparation coefficients are sqrt(x) I and x(E+zeta P), and the reader matrix B_R has rows (-x, sqrt(x) zeta^(-1)) and (sqrt(x) zeta^(-1), -x zeta^3). Their composition equals zeta^2 times these Kraus operators in each record coordinate. The theorem also proves equality of the resulting CP branches, so this common phase does not alter the retained history law. A reconstruction for one designated preparation alone does not establish that interpretation for arbitrary inputs."))),
                DescribeRole.Theorem))));

    private static Formula NativeFormula()
    {
        Formula P = X("P"), r = X("r"), h = X("h"), n = X("n"), e = X("e"), N = X("N");
        Formula state = Call("ofMatrixInverse", Call("val", r));
        Formula q = Call("re", Call("trace", Mul(P, state)));
        Formula x = C("x"), age = Call("ageProbability", q, n);
        Formula pn = Call("pow", x, Mul(D(2), n));
        Formula prefix = Call("replicate", n, C("true"));
        Formula prefixMass = Add(q, Mul(Sub(D(1), q), pn));
        Formula carrier = Call("Sum", Call("Fin", Add(N, D(1))), C("Unit"));
        Formula correct = Call("NativeCorrect", X("M"), P, r, e);
        Formula low = All("e", RealType(), Imp(Conj(LT(D(0), e), LT(e, Div(x, D(2)))),
            Some("N", NatType(), Conj(Equal(N, Call("cutoff", q, e)),
                All("n", NatType(), IffOf(LE(age, Mul(D(2), e)), LE(N, n))),
                Some("M", Call("Predictor", carrier), correct),
                Equal(Call("card", carrier), Add(N, D(2))),
                FinitePredictors(Imp(correct, LE(Add(N, D(2)), Call("card", X("S")))))))));
        Formula k0 = Call("kraus", P, C("false")), k1 = Call("kraus", P, C("true"));
        Formula port = Call("nativePort", P, X("b"));
        Formula conclusion = Conj(
            All("h", Call("List", C("Bool")), Conj(LT(D(0), Call("mass", P, state, h)),
                Equal(Call("nextZero", P, state, h),
                    Call("ite", Call("contains", h, C("false")), x,
                        Call("ageProbability", q, Call("length", h)))))),
            All("n", NatType(), Conj(Equal(Call("mass", P, state, prefix), prefixMass),
                Equal(Call("posterior", P, state, prefix), Div(q, prefixMass)))), low,
            All("e", RealType(), Imp(LE(Div(x, D(2)), e),
                Some("M", Call("Predictor", C("Unit")), correct))),
            FinitePredictors(new Formula.Not(Call("NativeCorrect", X("M"), P, r, D(0)))),
            Equal(Add(Mul(Call("conjTranspose", k0), k0), Mul(Call("conjTranspose", k1), k1)), D(1)),
            All("b", C("Bool"), Equal(port,
                Call("smul", Call("pow", C("zeta"), D(2)), Call("kraus", P, X("b"))))),
            All("b", C("Bool"), All("sigma", MatrixType(),
                Equal(Mul(Mul(port, X("sigma")), Call("conjTranspose", port)),
                    Call("branch", P, X("b"), X("sigma"))))),
            All("h", Call("List", C("Bool")), Imp(Call("contains", h, C("false")),
                Equal(Call("posterior", P, state, h), D(0)))));
        return All("d", NatType(), All("P", MatrixType(),
            All("r", Call("DensityState", Call("Fin", X("d"))),
                Imp(Conj(Equal(Mul(P, P), P), Call("IsHermitian", P), LT(D(0), q), LT(q, D(1))),
                    conclusion))));
    }

    private static Formula MatrixType() => Call("Matrix", Call("Fin", X("d")), Call("Fin", X("d")), ComplexType());

    private static Formula X(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula C(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(C(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Conj(params Formula[] items)
    {
        Formula value = items[^1];
        for (var i = items.Length - 2; i >= 0; --i)
            value = Logic(items[i], FormulaLogicOperator.And, value);
        return value;
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NatType() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(FormulaDsl.Id("C")));
    private static Formula FinitePredictors(Formula body) => All("S", C("Type"),
        All("inst", Call("Fintype", X("S")), All("M", Call("Predictor", X("S")), body)));
}
