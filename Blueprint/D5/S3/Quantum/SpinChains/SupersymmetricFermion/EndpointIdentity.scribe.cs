using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class EndpointIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: EndpointIdentity"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("EndpointIdentity", "EndpointIdentity", F0(),
                "The symmetrized anticommutator of Q and R is 2b²(c² n₁−a² nN) for every length N=3n and all real a,b,c. This operator equation imposes no nonzero-coupling hypothesis.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpoint_identity", "endpoint identity", F1(),
                "Local Jordan-Wigner products cancel the bulk hopping and four-site currents. Compression to the hard-core space and the remaining diagonal telescoping give the exact boundary occupation operator. The identity holds for all real period-three couplings, including b=0.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-endpointidentity-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(new Formula.Relation(Parenthesized(Seq(Call("EndpointIdentity"), Colon, N("Prop"))),
        FormulaRelationOperator.Equal, All("n", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(All("a",
        N("Real"), All("b", N("Real"), All("cc", N("Real"), new Formula.Apply(Parenthesized(Seq(N("q"), Mapsto,
        Parenthesized(new Formula.Apply(Parenthesized(Seq(N("r"), Mapsto, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("q")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("r")))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(N("r")), FormulaBinaryOperator.Multiply, Parenthesized(N("q")))))),
        FormulaBinaryOperator.Add, Parenthesized(Call("adjoint", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("q")), FormulaBinaryOperator.Multiply, Parenthesized(N("r")))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(N("r")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("q")))))))), FormulaRelationOperator.Equal, Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(N("b")), D(2))))), new Formula.Binary(Parenthesized(Call("smul", Call("asReal",
        new Formula.Power(Parenthesized(N("cc")), D(2))), Call("number", D(1)))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("smul", Call("asReal", new Formula.Power(Parenthesized(N("a")), D(2))), Call("number", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n")))))))))))),
        [Call("Rmat", new Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n"))),
        N("a"), N("b"), N("cc"))])))), [Call("Qmat", new Formula.Binary(Parenthesized(D(3)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("n"))), Call("periodThree", N("a"), N("b"),
        N("cc")))])))))))));

    private static Formula F1() =>
        Disp(All("n", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(All("a",
        N("Real"), All("b", N("Real"), All("cc", N("Real"), new Formula.Apply(Parenthesized(Seq(N("q"), Mapsto,
        Parenthesized(new Formula.Apply(Parenthesized(Seq(N("r"), Mapsto, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("q")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("r")))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(N("r")), FormulaBinaryOperator.Multiply, Parenthesized(N("q")))))),
        FormulaBinaryOperator.Add, Parenthesized(Call("adjoint", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("q")), FormulaBinaryOperator.Multiply, Parenthesized(N("r")))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(N("r")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("q")))))))), FormulaRelationOperator.Equal, Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(N("b")), D(2))))), new Formula.Binary(Parenthesized(Call("smul", Call("asReal",
        new Formula.Power(Parenthesized(N("cc")), D(2))), Call("number", D(1)))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("smul", Call("asReal", new Formula.Power(Parenthesized(N("a")), D(2))), Call("number", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n")))))))))))),
        [Call("Rmat", new Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n"))),
        N("a"), N("b"), N("cc"))])))), [Call("Qmat", new Formula.Binary(Parenthesized(D(3)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("n"))), Call("periodThree", N("a"), N("b"), N("cc")))]))))))));
}
