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
                    Paragraph(Text("For epsilon >= x/2 a single state outputting x/2 suffices. At epsilon=0 no finite predictor is correct, because the positive age probabilities tend to zero and a finite total-update orbit must repeat. Only the state count is asserted. The natural ceiling definition of N is the ceiling of log((1-q)(x-2 epsilon)/(2 epsilon q))/(2 log phi), truncated at zero; Nat.ceil_le gives the nonstrict threshold, including integer ties. The asymptotic state and bit bounds, exact-depth augmented predictors and the degenerate q endpoints lie outside the formal statement. Supplying depth changes the state contract by supplying a clock; it does not remove the counting resource.")),
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
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
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
