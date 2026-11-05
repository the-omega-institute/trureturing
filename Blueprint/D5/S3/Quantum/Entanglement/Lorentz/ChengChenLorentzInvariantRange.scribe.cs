using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Lorentz;

internal sealed class ChengChenLorentzInvariantRangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chengchen2026lorentzrange");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For odd n, the Lorentz invariant of n-qubit states has exactly the real interval [-1/2,0] as its range.",
        H("The odd-qubit Lorentz invariant range"), Blocks(
            Paragraph(Text(
                "All matrices have complex entries. The computational basis is the function type Fin n → Fin 2. "
                + "A state is positive semidefinite with trace one. The Levi-Civita matrix is the displayed real two-by-two matrix, "
                + "and epsN is its coordinatewise tensor power. The invariant is the trace in Eq. (54) of Cheng and Chen, "
                + "arXiv:2605.19530v2, Definition 12 and Conjecture 24.")),
            Node("eps", "The two-dimensional Levi-Civita symbol", "eps", EpsFormula(),
                "The matrix has rows and columns indexed by Fin 2 and entries 0, 1, -1, 0 in that order.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("epsN", "The tensor power", "epsN", EpsNFormula(),
                "For each natural n, epsN n has entry the finite product of eps at the corresponding bit coordinates.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("state", "An n-qubit state", "IsState", IsStateFormula(),
                "A matrix is a state exactly when it is positive semidefinite and has trace one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lorentz", "The Lorentz invariant", "lorentz", LorentzFormula(),
                "The invariant is Tr(rhoᵀ epsN n rho epsN n), the complex trace of the product in Eq. (54).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The range conjecture", "claim", ClaimBody(),
                "Conjecture 24 states verbatim: \"Suppose ρ is an arbitrary n-qubit state with odd n, then the range of Lorentz invariant Iρ is [−1/2, 0].\" (p. 12). The encoding takes the range as the set of complex values of lorentz on IsState matrices and the real interval as its complex image.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("cheng-chen-lorentz-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The conjectured range is proved"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "For odd n, epsN is skew-symmetric, squares to minus the identity, and is unitary. "
                        + "The Breuer positive-map estimate applied to a state A and its spin-flip partner B gives "
                        + "0 ≤ Re Tr(A B) ≤ 1/2. Cyclicity of trace identifies lorentz A with −Tr(A B), so every value lies in the stated interval.")),
                    Paragraph(Text(
                        "The diagonal pair state p|0⋯0⟩⟨0⋯0|+(1−p)|1⋯1⟩⟨1⋯1| has invariant −2p(1−p). "
                        + "Choosing p=(1−sqrt(1+2x))/2 attains every x in [−1/2,0]."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lorentzrange"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("cheng-chen-lorentz-" + id.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vec(Formula n) => new Formula.TypeArrow(Fin(n), Fin(D(2)));
    private static Formula Mat(Formula n) => Call("Matrix", Vec(n), Vec(n), C());
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Operator(name) : At(Operator(name), args);
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Product(string binder, Formula type, Formula body) => Seq(new Formula.Subscript(Prod, Cast(F.Id(binder), type)), Sp, Parenthesized(body));
    private static Formula MatrixLiteral() => Seq(Begin, Grp(F.Id("pmatrix")), D(0), Amp, D(1), RowBreak, Seq(Minus, D(1)), Amp, D(0), End, Grp(F.Id("pmatrix")));
    private static Formula EpsFormula() => Equal(Call("eps"), MatrixLiteral());

    private static Formula EpsNFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var body = Equal(At(Call("epsN"), n, i, j), Product("k", Fin(n), At(Call("eps"), At(i, k), At(j, k))));
        return All("n", N(), All("i", Vec(n), All("j", Vec(n), body)));
    }

    private static Formula IsStateFormula()
    {
        var n = F.Id("n");
        var rho = F.Id("rho");
        var body = Equal(At(Call("IsState"), rho), And(At(Qualified("Matrix", "PosSemidef"), rho), Equal(At(Qualified("Matrix", "trace"), rho), D(1))));
        return All("n", N(), All("rho", Mat(n), body));
    }

    private static Formula LorentzFormula()
    {
        var n = F.Id("n");
        var rho = F.Id("rho");
        var product = Seq(At(Qualified("Matrix", "transpose"), rho), Cdot, Sp, Call("epsN", n), Cdot, Sp, rho, Cdot, Sp, Call("epsN", n));
        return All("n", N(), All("rho", Mat(n), Equal(At(Call("lorentz"), rho), At(Qualified("Matrix", "trace"), product))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        var rho = F.Id("rho");
        var x = F.Id("x");
        var values = SetOf("z", C(), Ex("rho", Mat(n), And(At(Call("IsState"), rho), Equal(At(Call("lorentz"), rho), z))));
        var interval = At(Qualified("Set", "Icc"), Seq(Minus, Fraction(D(1), D(2))), D(0));
        var image = At(Qualified("Set", "image"), LambdaOf("x", R(), Cast(x, C())), interval);
        return All("n", N(), Imp(At(Operator("Odd"), n), Equal(values, image)));
    }

    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Cast(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Cast(F.Id(name), type), Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
}
