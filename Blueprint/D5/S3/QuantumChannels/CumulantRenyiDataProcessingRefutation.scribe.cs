using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class CumulantRenyiDataProcessingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/meunson2026cumulant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Meunson and Deesuwan (arXiv:2606.31205) define a cumulant-based quantum relative Renyi functional for alpha > 1 and state in the abstract and conclusion that its quantum data-processing inequality under arbitrary CPTP maps remains open. For every alpha > 1 a pair of positive definite qubit states and the complete dephasing channel increase the functional, so the inequality fails at every order above one.",
        H("Data processing fails for the cumulant-based Renyi functional at every order above one"),
        Blocks(
            Node("two-point-cfc", "Functional calculus for a self-adjoint involution", TwoPointFormula(),
                "For a self-adjoint complex matrix H with H squared equal to the identity, the spectrum lies in {1, -1}. For every real function f and real a and b, the function of a I + b H is the sum of the mean of f(a+b) and f(a-b) times I and half their difference times H. No continuity hypothesis on f is needed because the spectrum is finite.",
                "two_point_cfc", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("dephasing-action", "The action of complete dephasing",
                Disp(All(F.Id("A"), Mat(D(2)), Equal(Call("pinchingEnd", F.Id("A")),
                    Call("diagonal", Seq(Bang, OpenBracket,
                        new Formula.Apply(F.Id("A"), [D(0), D(0)]), Comma, Sp,
                        new Formula.Apply(F.Id("A"), [D(1), D(1)]), CloseBracket))))),
                "For every complex two by two matrix A, complete dephasing keeps its two diagonal entries and sets the off-diagonal entries to zero.",
                "dephase_apply", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("dephasing-kraus", "The Kraus representation of complete dephasing",
                Disp(Equal(Parenthesized(Seq(Named("pinchingEnd"), Sp, Colon, Sp, Map(D(2)))),
                    Call("ofKraus", BasisProjectors(), BasisProjectors()))),
                "For j in Fin 2, the family K(j)=single(j,j,1) consists of the two computational basis projectors. The linear map pinchingEnd is exactly their finite Kraus map, ofKraus(K,K).",
                "pinching_kraus", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("functional", "The cumulant-based relative Renyi functional", FunctionalFormula(),
                "Definition 3 of the paper, on faithful inputs: for complex d by d matrices A and B and real alpha, the value is 1/(alpha-1) times the real logarithm of the real part of Tr(A exp((alpha-1)(log A - log B))). Log of a matrix is continuous functional calculus for the real logarithm and exp is the matrix exponential, as in the frozen alpha-zero refutation for the same paper. On positive definite A and B the trace is a positive real number, and the formula is the paper's.",
                "cuRenyi", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("qdpi", "The data-processing inequality at alpha", DataProcessingFormula(),
                "Section III of the paper states data processing as S_alpha(rho||sigma) >= S_alpha(N(rho)||N(sigma)) for every CPTP map N and states with supp(rho) contained in supp(sigma). QDPI(alpha) states it for density matrices rho and sigma on C^d of every dimension d that are positive definite, for every CPTP map N on d by d complex matrices with positive definite outputs. IsDensity and IsCPTP are the frozen definitions of the alpha-zero refutation for the same paper. Faithful inputs satisfy the support condition, and faithful outputs need no convention for the logarithm of a singular matrix.",
                "QDPI", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Data processing for some order above one", ClaimFormula(),
                "The open question of the abstract and conclusion, in its weakest form: some alpha > 1 satisfies QDPI(alpha). Its negation refutes data processing at every order above one, already for faithful inputs and outputs.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "No order above one satisfies data processing", Disp(new Formula.Not(F.Id("claim"))),
                "Fix alpha > 1, put t = alpha - 1, x = 16^(1 + 1/t), r = (x - 1)/(x + 1) and a = (ln x)/2. Let N be the symmetric involution with rows (1/2, sqrt(3)/2) and (sqrt(3)/2, -1/2), and Z = diag(1, -1); then B = N - Z is also a self-adjoint involution. The states rho = (I + r N)/2 and sigma = (I + r Z)/2 are positive definite with trace one and common spectrum {x/(x+1), 1/(x+1)}. Two-point functional calculus gives log rho - log sigma = a B and exp(t a B) = cosh(t a) I + sinh(t a) B, so the input trace is cosh(t a) + (r/2) sinh(t a), which is less than exp(t a) = 4^(t+1). The complete dephasing channel with Kraus operators diag(1, 0) and diag(0, 1) is CPTP and sends rho and sigma to the positive definite diagonal matrices diag(p+, p-) and diag(q+, q-) with p- = (x+3)/(4(x+1)) > 1/4 and q- = 1/(x+1). The output trace is p+^(t+1) q+^(-t) + p-^(t+1) q-^(-t) > (1/4) ((x+3)/4)^t > (1/4) (x/4)^t = 4^(t+1). By strict monotonicity of the logarithm and 1/t > 0 the functional increases under the channel, contradicting QDPI(alpha).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meunson-deesuwan-2026-cumulant-renyi-qdpi"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("curenyi-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula BasisProjectors() => Parenthesized(Seq(LambdaLower, Sp, F.Id("j"), Sp,
        Colon, Sp, Call("Fin", D(2)), Comma, Sp,
        Call("single", F.Id("j"), F.Id("j"), D(1))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) =>
        Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MinusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Scalar(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(Formula d) => Seq(Complexes(), Caret, Grp(d, F.Times, Sp, d));
    private static Formula Map(Formula d) => Call("MatrixMap", Call("Fin", d), Call("Fin", d), Complexes());
    private static Formula Apply(Formula n, Formula a) => new Formula.Apply(n, [a]);
    private static Formula CuRenyi(Formula alpha, Formula a, Formula b) => Call("cuRenyi", alpha, a, b);

    private static Formula TwoPointFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), a = F.Id("a"), b = F.Id("b"), h = F.Id("H");
        Formula matrix = Call("Matrix", n, n, Complexes());
        Formula plus = new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula fp = Apply(f, plus), fm = Apply(f, MinusOf(a, b));
        Formula mean = new Formula.Fraction(new Formula.Binary(fp, FormulaBinaryOperator.Add, fm), D(2));
        Formula difference = new Formula.Fraction(MinusOf(fp, fm), D(2));
        Formula input = new Formula.Binary(Scalar(a, D(1)), FormulaBinaryOperator.Add, Scalar(b, h));
        Formula output = new Formula.Binary(Scalar(mean, D(1)), FormulaBinaryOperator.Add, Scalar(difference, h));
        Formula equation = Equal(Call("cfc", f, input), output);
        Formula body = Implies(Call("IsSelfAdjoint", h), Implies(Equal(TimesOf(h, h), D(1)), equation));
        Formula quantified = All(n, Named("Type"), Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
            All(f, new Formula.TypeArrow(Reals(), Reals()),
                All(a, Reals(), All(b, Reals(), All(h, matrix, body))))));
        return Disp(quantified);
    }

    private static Formula FunctionalFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A"), b = F.Id("B");
        Formula alphaMinusOne = Parenthesized(MinusOf(Alpha, D(1)));
        Formula delta = Parenthesized(MinusOf(Call("log", a), Call("log", b)));
        Formula trace = Call("Re", Call("Tr", TimesOf(a, Call("exp", Scalar(alphaMinusOne, delta)))));
        Formula value = TimesOf(new Formula.Fraction(D(1), alphaMinusOne), Call("ln", trace));
        return Disp(All(d, Naturals(), All(Alpha, Reals(), All(a, Mat(d), All(b, Mat(d),
            Equal(CuRenyi(Alpha, a, b), value))))));
    }

    private static Formula DataProcessingFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N");
        Formula nr = Apply(n, Rho), ns = Apply(n, SigmaLower);
        Formula monotone = Leq(CuRenyi(Alpha, nr, ns), CuRenyi(Alpha, Rho, SigmaLower));
        Formula body = Implies(Call("IsDensity", Rho), Implies(Call("IsDensity", SigmaLower),
            Implies(Call("PosDef", Rho), Implies(Call("PosDef", SigmaLower),
                Implies(Call("IsCPTP", n), Implies(Call("PosDef", nr),
                    Implies(Call("PosDef", ns), monotone)))))));
        Formula quantified = All(d, Naturals(), All(Rho, Mat(d), All(SigmaLower, Mat(d),
            All(n, Map(d), body))));
        return Disp(All(Alpha, Reals(), Iff(Call("QDPI", Alpha), quantified)));
    }

    private static Formula ClaimFormula() =>
        Disp(Iff(F.Id("claim"), Some(Alpha, Reals(),
            And(Less(D(1), Alpha), Call("QDPI", Alpha)))));
}
