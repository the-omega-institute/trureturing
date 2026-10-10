using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class PeritoTsirelsonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/perito2026bell");
    private const string Prefix = "D5/S3/QuantumBounds/PeritoTsirelson.";
    private static readonly Formula Dd = F.Id("d"), N = F.Id("n"), M = F.Id("m"),
        Aa = F.Id("a"), Bb = F.Id("b"), A = F.Id("A"), B = F.Id("B"),
        R = F.Id("rho"), X = F.Id("x"), Y = F.Id("y"), I = F.Id("i"), J = F.Id("j"),
        Iota = F.Id("iota");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite unitary strategy satisfies the Perito Bell upper bound. The cyclic clock, shift and normalized maximally entangled state give a valid strategy attaining the bound.",
        H("The Perito Bell bound and its attaining strategy"),
        Blocks(
            Paragraph(Text(
                "The outcome count is d, Alice has two settings and Bob has d settings. " +
                "Their finite local dimensions n and m are arbitrary. All matrix norms " +
                "are operator norms for the Euclidean vector norm. The phase windowRoot(d) " +
                "is exp(2 pi i/d), and kronecker denotes the matrix tensor product. " +
                "Bob's cyclic matrices are the coefficient sums of shift to the power k+1 times clock to the power k. " +
                "For y and k from zero to d minus one, lambda(y,k) is " +
                "(-1)^k omega^(k(k+1)/2) omega^(-y(1+k)) divided by " +
                "d sin(pi(k+1/2)/d), where omega = windowRoot(d). " +
                "Write nu(j) = exp(pi i (2j+1)/d) and " +
                "g(t) = sum_k t^k/(d sin(pi(k+1/2)/d)). In these phases i is the " +
                "imaginary unit, and val(j) is the representative of j between zero and d minus one. " +
                "DensityState(a) consists of positive semidefinite complex matrices indexed " +
                "by a with trace one. Adjoint means conjugate transpose.")),
            Describe.Lean(
                DescribeId.Create("the-cosecant-polynomial-at-the-roots-of-minus-one"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoTsirelson.peritoG_at_nu"),
                H("Finite Fourier evaluation"),
                StatementSource.FromAuthor(Disp(All(Dd, Nat(), NonzeroDimension(All(J, Cyclic(),
                    Eq(Call("peritoG", Dd, Call("peritoNu", Dd, J)),
                        Call("exp", Mul(Mul(Div(Pi, Mul(D(2), Dd)),
                            Seq(Open, Dd, Minus, D(1), Minus, Mul(D(2), Call("val", J)), Close)), I)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the discrete Fourier transform to " +
                        "i exp(-pi i (j+1/2)/d). Its k-th transform coefficient is " +
                        "exp(pi i k/d)/sin(pi(k+1/2)/d). To see this, the ratio " +
                        "r=exp(-pi i (2k+1)/d) has r^d=-1, and the geometric sum " +
                        "is 2/(1-r). Euler's identity reduces its denominator to " +
                        "2i exp(-pi i (k+1/2)/d) sin(pi(k+1/2)/d). " +
                        "The sine is positive for zero through d minus one.")),
                    Paragraph(Text(
                        "Fourier inversion then gives the polynomial value. Combining " +
                        "the leading i with the exponential yields the centered phase " +
                        "shown above. The identity holds for every positive integer d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-cyclic-bob-matrices-are-unitary"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoTsirelson.peritoB_unitary"),
                H("Unitarity"),
                StatementSource.FromAuthor(Disp(BobContext(All(Y, Fin(Dd),
                    Unitary(Bob(Y), Cyclic()))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Put u_y = -omega^(1-y) XZ. The triangular Weyl phase gives " +
                        "u_y^d=-I. The coefficients yield B_y=omega^(-y) X g(u_y). " +
                        "The generators, their product, and the scalar prefactors are unitary.")),
                    Paragraph(Text(
                        "Any polynomial vanishing at all nu_j is divisible by t^d+1, " +
                        "since these roots are distinct. Thus equal polynomial values " +
                        "at every nu_j give equal evaluations at u_y. For a unitary u " +
                        "with u^d=-I, its adjoint is -u^(d-1). The coefficients of g " +
                        "are real, so its adjoint is represented by g(-t^(d-1)). " +
                        "On each nu_j this is the conjugate of g(nu_j). The Fourier " +
                        "evaluation has modulus one, so the product is one at every " +
                        "root. Polynomial divisibility then gives g(u_y)g(u_y)^*=I, " +
                        "and hence B_y is unitary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-cyclic-bob-matrices-have-d-th-power-one"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoTsirelson.peritoB_pow"),
                H("The d-th power"),
                StatementSource.FromAuthor(Disp(BobContext(All(Y, Fin(Dd),
                    Eq(Pow(Bob(Y), Dd), D(1)))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The Weyl relation gives u_y X = X (omega u_y). " +
                        "For every polynomial p, it follows that p(u_y)X = Xp(omega u_y). " +
                        "Iterating this identity shows that (Xg(u_y))^d is " +
                        "X^d times the evaluation at u_y of the product of " +
                        "g(omega^j t) for zero through d minus one.")),
                    Paragraph(Text(
                        "Multiplication by omega permutes all roots of minus one. " +
                        "At each such root, the product is the product of all " +
                        "exp(pi i (d-1-2j)/(2d)). The exponents sum to zero, " +
                        "so this product is one. Divisibility by t^d+1 transfers " +
                        "the equality to u_y. Finally X^d=I and " +
                        "(omega^(-y))^d=1 give B_y^d=I."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("validity-and-trace-attainment-of-the-cyclic-bob-strategy"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoTsirelson.peritoB_spec"),
                H("Validity and attained value"),
                StatementSource.FromAuthor(Disp(BobContext(And(All(Y, Fin(Dd),
                    And(Unitary(Bob(Y), Cyclic()), Eq(Pow(Bob(Y), Dd), D(1)))), BobTraceSum())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For d at least two, every B_y is unitary and has d-th power " +
                    "identity. Together with these properties, the statement includes " +
                    "the exact trace-sum equality displayed below. Thus the same " +
                    "matrices satisfy both observable validity and trace attainment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-cyclic-bob-trace-pairing-sum"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoTsirelson.peritoB_attained_sum"),
                H("Exact trace sum"),
                StatementSource.FromAuthor(Disp(BobContext(BobTraceSum()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Trace cyclicity and displacement trace orthogonality eliminate " +
                        "every term except k=d-1 in tr(Z^T B_y) and k=0 in tr(X^T B_y). " +
                        "The endpoint coefficients give 1/sin(pi/(2d)) and " +
                        "omega^(-y)/sin(pi/(2d)), respectively.")),
                    Paragraph(Text(
                        "The endpoint phase is fixed by omega^((d-1)d/2)=(-1)^(d-1), " +
                        "and sin(pi-pi/(2d))=sin(pi/(2d)). Multiplication by omega^y " +
                        "therefore makes the two traces equal. Summing over all d settings " +
                        "gives the displayed complex identity. Dividing by d gives the " +
                        "corresponding maximally entangled trace-pairing value."))),
                DescribeRole.Theorem),
            Def("IsDObservable", "root-of-unity-observable", "Root-of-unity observables",
                All(Dd, Nat(), Index(Aa, All(A, Mat(Aa), Iff(Obs(A),
                    And(Unitary(A, Aa), Eq(Pow(A, Dd), D(1))))))),
                "A d-observable is a unitary matrix whose d-th power is the identity. " +
                "Its eigenvalues are therefore d-th roots of unity."),
            Def("bellOperator", "perito-bell-operator", "Bell operator",
                Strategies(Eq(Call("bellOperator", Dd, A, B),
                    SumOver(X, Fin(D(2)), SumOver(Y, Fin(Dd),
                        Mul(Pow(Call("windowRoot", Dd), Mul(X, Y)),
                            Tensor(App(A, X), App(B, Y))))))),
                "The Bell matrix is the sum of windowRoot(d) raised to xy times A(x) " +
                "tensor B(y). It need not be Hermitian. Its Hermitian part is the " +
                "Bell observable.", literature: true),
            Def("bellValue", "real-bell-expectation", "Real Bell expectation",
                Strategies(All(R, Mat(Product(Aa, Bb)), Eq(Call("bellValue", Dd, A, B, R),
                    RePart(Trace(Mul(R, Call("bellOperator", Dd, A, B))))))),
                "The Bell value is the real part of trace(rho times the Bell matrix). " +
                "For a Hermitian density matrix this equals the expectation of the " +
                "Hermitian part of the Bell matrix.", literature: true),
            Def("maxEntangledVector", "maximally-entangled-amplitudes", "Entangled amplitudes",
                Index(Iota, All(I, Product(Iota, Iota),
                    Eq(Call("maxEntangledVector", Iota, I),
                        Call("ite", Eq(Call("fst", I), Call("snd", I)),
                            Pow(Call("sqrt", Call("card", Iota)), Negative(D(1))), D(0))))),
                "For any finite index type iota, the amplitude on a pair of basis labels " +
                "is the real reciprocal of sqrt(card(iota)), cast to a complex number, " +
                "when the labels coincide and zero otherwise. The function ite chooses " +
                "its second argument when its first argument is true, and its third otherwise.", literature: true),
            Def("maxEntangled", "maximally-entangled-matrix", "Entangled matrix",
                Index(Iota, Eq(Call("maxEntangled", Iota),
                    Call("vecMulVec", Call("maxEntangledVector", Iota),
                        Call("star", Call("maxEntangledVector", Iota))))),
                "The matrix is the outer product of the entangled vector with its " +
                "entrywise conjugate. Thus it is a positive rank-one matrix when iota is nonempty. " +
                "The cyclic strategy uses iota = ZMod(d).", literature: true),
            Def("claim", "perito-bound-and-cyclic-equality", "Bound and cyclic equality",
                Iff(F.Id("claim"), SettlementClaim()),
                "For every d at least two, the claim combines five assertions: the " +
                "upper bound for every finite projective strategy and density state; " +
                "validity of the cyclic clock and shift; validity of Bob's cyclic " +
                "matrices; positivity and trace one of the entangled matrix; and " +
                "equality with 2/sin(pi/(2d)) for this cyclic strategy. The local " +
                "dimensions in the first assertion include zero. The cyclic " +
                "matrices in the remaining assertions use the basis ZMod(d).", literature: true),
            Theorem("bell_value_le", "perito-unitary-upper-bound", "Upper bound for unitary strategies",
                All(Dd, Nat(), Imp(Le(D(2), Dd), UnitaryBound())),
                "Only unitarity is required for the upper bound; no d-th-power relation " +
                "is used. Put U = adjoint(A(0)) times A(1), which is unitary. " +
                "Expanding the two Alice settings and distributing the tensor product gives " +
                "bellOperator = (A(0) tensor I) times the sum over y of " +
                "(I + windowRoot(d)^y U) tensor B(y). Left multiplication by the " +
                "unitary A(0) tensor I preserves the operator norm, including on a " +
                "zero-dimensional space. On a nonzero space this factor has norm one. " +
                "The unitary tensor block bound reduces the remaining norm to the " +
                "uniform scalar sum of |1 + windowRoot(d)^y z| for |z| = 1. " +
                "That scalar sum is at most 2/sin(pi/(2d)).",
                "For a density matrix rho and an arbitrary matrix T, let " +
                "H = (T + adjoint(T))/2. The triangle inequality gives norm(H) " +
                "at most norm(T). Self-adjointness gives H at most norm(H) times I " +
                "in the positive semidefinite order. The real trace of the product " +
                "of two positive semidefinite matrices is nonnegative. Applying this " +
                "to rho and norm(H) I - H, and using trace(rho) = 1, gives " +
                "Re trace(rho H) at most norm(H). Trace cyclicity and Hermitian " +
                "rho identify Re trace(rho H) with Re trace(rho T). This proves " +
                "the density expectation bound and hence the Bell upper bound."),
            Theorem("clock_shift_observables", "cyclic-alice-observables", "Clock and shift observables",
                All(Dd, Nat(), NonzeroDimension(AliceObservable())),
                "The finite clock and shift are unitary, and each returns to the " +
                "identity after d powers. Selecting either of the two settings " +
                "therefore gives a d-observable."),
            Theorem("max_entangled_density", "entangled-density-normalization", "Entangled density normalization",
                Index(Iota, NonemptyIndex(Iota, EntangledDensity(Iota))),
                "Every outer product v v adjoint is positive semidefinite. The trace " +
                "is the sum of the squared moduli of the vector entries. There are " +
                "exactly card(iota) nonzero entries, one for each equal pair of basis labels, " +
                "and each has squared modulus 1/card(iota). Since iota is nonempty, the trace is one."),
            Theorem("max_entangled_trace", "entangled-transpose-expectation", "Transpose expectation identity",
                Index(Iota, NonemptyIndex(Iota, All(A, Mat(Iota), All(B, Mat(Iota),
                    Eq(Trace(Mul(Call("maxEntangled", Iota), Tensor(A, B))),
                        Div(Trace(Mul(Call("transpose", A), B)), Call("card", Iota))))))),
                "The diagonal correlations in the entangled vector restrict both pairs of " +
                "basis indices to equal labels. Expanding the trace therefore gives " +
                "the sum of A(j,i) B(j,i) divided by card(iota). This is " +
                "trace(transpose(A) B)/card(iota). " +
                "The transpose is ordinary transpose, without complex conjugation."),
            Describe.Lean(DescribeId.Create("perito-tsirelson-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Sharp bound in every outcome count"),
                StatementSource.FromAuthor(Disp(SettlementClaim())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The upper bound applies to every finite projective strategy because its " +
                    "observables are unitary. The clock and shift are unitary with d-th power " +
                    "one. Bob's polynomial observables are unitary with d-th power one, and " +
                    "the maximally entangled matrix is positive with trace one. Thus the " +
                    "cyclic strategy is valid.")),
                    Paragraph(Text(
                    "Expand the two Alice settings in the Bell operator and distribute the " +
                    "trace over Bob's settings. The transpose expectation identity makes the " +
                    "complex expectation equal to the sum of trace(transpose(Z) B(y)) plus " +
                    "omega^y trace(transpose(X) B(y)), divided by d. The clock-shift trace " +
                    "sum is d times 2/sin(pi/(2d)). Cancelling the nonzero dimension and " +
                    "taking the real part gives exactly 2/sin(pi/(2d)). The attained value " +
                    "equals the universal upper bound, so it is the Tsirelson bound."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("perito-2026-tsirelson-bound-id"), ResolutionKind.Proved)))));


    private static DocumentBlock.Describe Def(string name, string id, string title, Formula statement, string text, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock.Describe Theorem(string name, string id, string title, Formula statement,
        string text, string? second = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            second is null ? Blocks(Paragraph(Text(text))) :
                Blocks(Paragraph(Text(text)), Paragraph(Text(second))), DescribeRole.Theorem);

    private static Formula Bound() => Div(D(2), Call("sin", Div(Pi, Mul(D(2), Dd))));
    private static Formula Bob(Formula y) => Call("peritoB", Dd, y);
    private static Formula BobContext(Formula body) => All(Dd, Nat(),
        NonzeroDimension(Imp(Le(D(2), Dd), body)));
    private static Formula BobTraceSum() => Eq(SumOver(Y, Fin(Dd), Seq(Open,
        Trace(Mul(Call("transpose", Call("clockMatrix", Dd)), Bob(Y))), Plus,
        Mul(Pow(Call("windowRoot", Dd), Call("val", Y)),
            Trace(Mul(Call("transpose", Call("shiftMatrix", Dd)), Bob(Y)))), Close)),
        Mul(Dd, Bound()));
    private static Formula Alice() => Seq(OpenBracket, Call("clockMatrix", Dd), Comma, Sp,
        Call("shiftMatrix", Dd), CloseBracket);
    private static Formula SettlementClaim() => All(Dd, Nat(), Imp(Le(D(2), Dd),
        And(ProjectiveBound(), And(AliceObservable(),
            And(All(Y, Fin(Dd), Obs(Call("peritoB", Dd, Y))),
                And(EntangledDensity(Cyclic()), CyclicEquality()))))));
    private static Formula Cyclic() => Call("ZMod", Dd);
    private static Formula Obs(Formula a) => Call("IsDObservable", Dd, a);
    private static Formula AliceObservable() => All(X, Fin(D(2)), Obs(App(Alice(), X)));
    private static Formula EntangledDensity(Formula index) => And(
        Le(D(0), Call("ofMatrix", Call("maxEntangled", index))),
        Eq(Trace(Call("maxEntangled", index)), D(1)));
    private static Formula CyclicEquality() => Eq(Call("bellValue", Dd, Alice(),
        Call("peritoB", Dd), Call("maxEntangled", Cyclic())), Bound());
    private static Formula ProjectiveBound() => Dimensions(All(A, Arrow(Fin(D(2)), Mat(Fin(N))),
        All(B, Arrow(Fin(Dd), Mat(Fin(M))), All(R, Call("DensityState", Product(Fin(N), Fin(M))),
            Imp(All(X, Fin(D(2)), Obs(App(A, X))), Imp(All(Y, Fin(Dd), Obs(App(B, Y))),
                Le(Call("bellValue", Dd, A, B, R), Bound())))))));
    private static Formula UnitaryBound() => Dimensions(All(A, Arrow(Fin(D(2)), Mat(Fin(N))),
        All(B, Arrow(Fin(Dd), Mat(Fin(M))), All(R, Call("DensityState", Product(Fin(N), Fin(M))),
            Imp(All(X, Fin(D(2)), Unitary(App(A, X), Fin(N))),
            Imp(All(Y, Fin(Dd), Unitary(App(B, Y), Fin(M))),
                Le(Call("bellValue", Dd, A, B, R), Bound())))))));
    private static Formula Strategies(Formula body) => All(Dd, Nat(), Index(Aa, Index(Bb,
        All(A, Arrow(Fin(D(2)), Mat(Aa)), All(B, Arrow(Fin(Dd), Mat(Bb)), body)))));
    private static Formula Dimensions(Formula body) => All(N, Nat(), All(M, Nat(), body));
    private static Formula Index(Formula a, Formula body) => All(a, F.Id("Type"), Seq(
        OpenBracket, Call("Fintype", a), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", a), CloseBracket, Sp, body));
    private static Formula NonzeroDimension(Formula body) => Seq(
        OpenBracket, Call("NeZero", Dd), CloseBracket, Sp, body);
    private static Formula NonemptyIndex(Formula index, Formula body) => Seq(
        OpenBracket, Call("Nonempty", index), CloseBracket, Sp, body);
    private static Formula Unitary(Formula a, Formula index) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, Call("unitaryGroup", index, Complex()));
    private static Formula Mat(Formula index) => Call("Matrix", index, index, Complex());
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Product(Formula a, Formula b) => Seq(Open, a, Sp, Times, Sp, b, Close);
    private static Formula Tensor(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula Trace(Formula a) => Call("trace", a);
    private static Formula RePart(Formula a) => Call("re", a);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, name, Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula SumOver(Formula name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(name, Sp, InMacro, Sp, type), Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Negative(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
}
