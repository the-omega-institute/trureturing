using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class RenyiInformationCombiningOrderThreeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hircheguantomamichel2023renyicombining");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both branches of the binary quantum information-combining expression are equalities "
            + "at Renyi order three, in arbitrary finite dimensions including singular marginals.",
        H("Order-three Renyi information combining"),
        Blocks(
            Node("conditional-entropy", "condRenyiDown", "Sandwiched conditional Renyi entropy",
                CondFormula(),
                "Section IV, p. 4, defines the sandwiched conditional Renyi entropy by the "
                    + "trace of the alpha power of the sandwiched state. The identity on A is "
                    + "explicit here; partialTraceLeft is the B marginal. Matrix real powers "
                    + "are continuous-functional-calculus powers, with inverse powers taken on "
                    + "the support. Real.log uses natural logarithms. The real part of the trace "
                    + "is explicit. The equation applies to all matrices; its entropy "
                    + "interpretation is for density matrices and admissible alpha.",
                DescribeRole.Definition),
            Node("binary-input", "cqState", "Equiprobable classical-quantum input",
                CqFormula(),
                "Section V, p. 5: the two classical labels are equiprobable. Matrix.single "
                    + "is the matrix unit representing each classical basis projector. "
                    + "The two quantum blocks have the same finite-dimensional carrier.",
                DescribeRole.Definition),
            Node("combined-state", "tau", "The CNOT state",
                TauFormula(),
                "Section V, p. 5, states verbatim: \"After applying a CNOT gate to the classical "
                    + "systems we have the joint state\". Its displayed sum is encoded below. "
                    + "Addition in Fin 2 is XOR, and the index order is ((X1 + X2, X2), (B1, B2)). "
                    + "The quantum inputs are independent; each of the four classical pairs "
                    + "has weight one quarter.",
                DescribeRole.Definition),
            Node("trace-second-bit", "traceOutX2", "Discarding the second classical register",
                TraceFormula(),
                "The B carrier here may itself be a product. The partial trace sums over "
                    + "the diagonal X2 index, leaving X1 + X2 and B. This is the marginal "
                    + "used on the left of Conjecture V.5.",
                DescribeRole.Definition),
            Node("binary-entropy", "hRenyi", "Binary Renyi entropy",
                EntropyFormula(),
                "Page 2, before Theorem I.1: \"In the following, we denote the binary Rényi entropy "
                    + "as hα.\" The formula is the binary specialization of Renyi entropy "
                    + "with natural logarithms. Real powers are explicit in its Lean definition.",
                DescribeRole.Definition),
            Node("restricted-inverse", "hRenyiInv", "The binary-entropy inverse branch",
                InverseFormula(),
                "Function.invFunOn restricts the probability input to the closed interval "
                    + "[0, 1/2]. At alpha = 3, hRenyi maps this interval bijectively to "
                    + "[0, Real.log 2]. Consequently the entropy arguments of this inverse "
                    + "belong to [0, Real.log 2], and its returned probabilities lie in [0, 1/2].",
                DescribeRole.Definition),
            Node("binary-convolution", "bconv", "Binary convolution",
                ConvolutionFormula(),
                "The star in the source denotes binary convolution: the probability that "
                    + "two independent binary variables have different values.",
                DescribeRole.Definition),
            Node("source-claim", "claim", "The order-three equality clause",
                ClaimFormula(),
                "Conjecture V.5, Section V, p. 7, states verbatim: \"For α ∈ [2, 3] the same "
                    + "holds with ≥ exchanged by ≤ and for α ∈ {2, 3} the above holds with "
                    + "equality.\" The specialization alpha = 3 "
                    + "quantifies over all dimensions n1 and n2 and all four density matrices. "
                    + "The two displayed guards match the two source branches, including "
                    + "their common boundary. IsDensity is the existing predicate for a "
                    + "positive semidefinite complex matrix of trace one.",
                DescribeRole.Definition),
            Node("equality", "result", "Both order-three branches hold",
                Disp(Seq(Operatorname, Grp(F.Id("claim")))),
                "At order three the sandwich exponent is -1/3. Write the two sandwiched "
                    + "blocks as A and B, and set S = A + B and D = A - B. Their cubic "
                    + "trace equals (1 + 3 trace(S D D))/4. The XOR moment factorizes as "
                    + "the product of the input moments, because the quantum marginals "
                    + "are tensor products and their functional-calculus powers factorize. "
                    + "Positivity bounds each input entropy between zero and Real.log 2. "
                    + "Binary convolution multiplies the biases, yielding both expressions "
                    + "in claim. Singular marginals and noncommuting input matrices are included. "
                    + "The source's order-two equality (V.13) is cited, not "
                    + "formalized here. Other-order inequality clauses remain open.",
                DescribeRole.Theorem, derived: true))));

    private static DocumentBlock Node(string id, string name, string title,
        Formula formula, string prose, DescribeRole role, bool derived = false) =>
        Describe.Lean(DescribeId.Create("renyi-three-" + id),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role,
            derived ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hirche-guan-tomamichel-2023-renyi-order-three-equality"),
                ResolutionKind.Proved) : null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff2(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Plus2(Formula left, Formula right) => Add(left, right);
    private static Formula Minus2(Formula left, Formula right) => Subtract(left, right);
    private static Formula Times2(Formula left, Formula right) => Multiply(left, right);
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TypeType() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula ProdType(Formula a, Formula b) =>
        Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Mat(Formula n) => Call("Matrix", n, n, ComplexType());
    private static Formula Tensor(Formula a, Formula b) => App(Q("Matrix", "kronecker"), a, b);
    private static Formula Scale(Formula a, Formula b) => App(Q("HSMul", "hSMul"), a, b);
    private static Formula Single(Formula i) => App(Q("Matrix", "single"), i, i, Num(1));
    private static Formula LogOf(Formula x) => App(Q("Real", "log"), x);
    private static Formula Finite(string name, Formula body) => All(name, TypeType(), Seq(
        OpenBracket, Call("Fintype", F.Id(name)), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id(name)), CloseBracket, Sp, body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, body);
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Seq(
        Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Colon, Sp, type, Sp,
        Eq, Sp, value, Semi, Sp, body);

    private static Formula CondFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), rho = F.Id("rho"), alpha = F.Id("alpha");
        Formula exponent = Divide(Minus2(Num(1), alpha), Times2(Num(2), alpha));
        Formula marginal = App(Q("PartialTraceMutualInformation", "partialTraceLeft"), rho);
        Formula m = Tensor(Typed(Num(1), Mat(a)), Parenthesized(Pow(marginal, exponent)));
        Formula product = Times2(Times2(F.Id("M"), rho), F.Id("M"));
        Formula rhs = Times2(Divide(Num(1), Minus2(Num(1), alpha)),
            LogOf(App(Q("RCLike", "re"), App(Q("Matrix", "trace"), Pow(product, alpha)))));
        Formula equation = Eqn(Call("condRenyiDown", alpha, rho), rhs);
        return Disp(Finite("a", Finite("b", All("alpha", RealType(),
            All("rho", Mat(ProdType(a, b)), Let("M", Mat(ProdType(a, b)), m, equation))))));
    }

    private static Formula CqFormula()
    {
        Formula n = F.Id("n"), s0 = F.Id("s0"), s1 = F.Id("s1");
        Formula half = Typed(Divide(Num(1), Num(2)), ComplexType());
        return Disp(All("n", TypeType(), All("s0", Mat(n), All("s1", Mat(n),
            Eqn(Call("cqState", s0, s1), Plus2(Scale(half, Tensor(Single(Num(0)), s0)),
                Scale(half, Tensor(Single(Num(1)), s1))))))));
    }

    private static Formula TauFormula()
    {
        Formula n1 = F.Id("n1"), n2 = F.Id("n2"), s1 = F.Id("s1"), s2 = F.Id("s2");
        Formula z = F.Id("z"), x2 = F.Id("x2");
        Formula term = Scale(Typed(Divide(Num(1), Num(4)), ComplexType()),
            Tensor(Single(Pair(Plus2(z, x2), x2)), Tensor(App(s1, z), App(s2, x2))));
        return Disp(All("n1", TypeType(), All("n2", TypeType(),
            All("s1", Arrow(Fin(Num(2)), Mat(n1)),
            All("s2", Arrow(Fin(Num(2)), Mat(n2)), Eqn(Call("tau", s1, s2),
                SumOver("z", Fin(Num(2)), SumOver("x2", Fin(Num(2)), term))))))));
    }

    private static Formula TraceFormula()
    {
        Formula b = F.Id("b"), t = F.Id("t"), z = F.Id("z"), j = F.Id("j");
        Formula w = F.Id("w"), k = F.Id("k"), x2 = F.Id("x2");
        Formula rhs = SumOver("x2", Fin(Num(2)),
            App(t, Pair(Pair(z, x2), j), Pair(Pair(w, x2), k)));
        return Disp(All("b", TypeType(), All("t", Mat(ProdType(
            ProdType(Fin(Num(2)), Fin(Num(2))), b)), All("z", Fin(Num(2)),
            All("j", b, All("w", Fin(Num(2)), All("k", b,
                Eqn(App(Call("traceOutX2", t), Pair(z, j), Pair(w, k)), rhs))))))));
    }

    private static Formula EntropyFormula()
    {
        Formula alpha = F.Id("alpha"), p = F.Id("p");
        return Disp(All("alpha", RealType(), All("p", RealType(),
            Eqn(Call("hRenyi", alpha, p), Times2(Divide(Num(1), Minus2(Num(1), alpha)),
                LogOf(Plus2(Pow(p, alpha), Pow(Minus2(Num(1), p), alpha))))))));
    }

    private static Formula InverseFormula()
    {
        Formula alpha = F.Id("alpha");
        return Disp(All("alpha", RealType(), Eqn(Call("hRenyiInv", alpha),
            App(Q("Function", "invFunOn"), Call("hRenyi", alpha),
                App(Q("Set", "Icc"), Num(0), Divide(Num(1), Num(2)))))));
    }

    private static Formula ConvolutionFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        return Disp(All("p", RealType(), All("q", RealType(), Eqn(Call("bconv", p, q),
            Plus2(Times2(p, Minus2(Num(1), q)), Times2(Minus2(Num(1), p), q))))));
    }

    private static Formula Density(Formula s) => All("x", Fin(Num(2)),
        App(Q("GHZMeasureBiseparableBound", "IsDensity"), App(s, F.Id("x"))));

    private static Formula ClaimFormula()
    {
        Formula n1 = F.Id("n1"), n2 = F.Id("n2"), s1 = F.Id("s1"), s2 = F.Id("s2");
        Formula h1 = F.Id("H1"), h2 = F.Id("H2"), hout = F.Id("Hout");
        Formula log2 = LogOf(Num(2)), sum = Plus2(h1, h2);
        Formula first = Call("hRenyi", Num(3), Call("bconv",
            Call("hRenyiInv", Num(3), h1), Call("hRenyiInv", Num(3), h2)));
        Formula second = Plus2(Minus2(sum, log2), Call("hRenyi", Num(3), Call("bconv",
            Call("hRenyiInv", Num(3), Minus2(log2, h1)),
            Call("hRenyiInv", Num(3), Minus2(log2, h2)))));
        Formula branches = And(Imp(Leq(sum, log2), Eqn(hout, first)),
            Imp(Leq(log2, sum), Eqn(hout, second)));
        Formula quantities = Let("H1", RealType(), Call("condRenyiDown", Num(3),
            Call("cqState", App(s1, Num(0)), App(s1, Num(1)))),
            Let("H2", RealType(), Call("condRenyiDown", Num(3),
                Call("cqState", App(s2, Num(0)), App(s2, Num(1)))),
            Let("Hout", RealType(), Call("condRenyiDown", Num(3),
                Call("traceOutX2", Call("tau", s1, s2))), branches)));
        Formula statement = All("n1", NatType(), All("n2", NatType(),
            All("s1", Arrow(Fin(Num(2)), Mat(Fin(n1))),
            All("s2", Arrow(Fin(Num(2)), Mat(Fin(n2))),
                Imp(Density(s1), Imp(Density(s2), quantities))))));
        return Disp(Iff2(Seq(Operatorname, Grp(F.Id("claim"))), statement));
    }
}
