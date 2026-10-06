using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class CubicProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicProducts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: CubicProducts"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("fullQ_split_localized", "fullQ split localized", F0(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("symOp", "symOp", F1(),
                "The displayed equation defines symOp.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("creatorNeighbourTerms", "creatorNeighbourTerms", F3(),
                "The displayed equation defines creatorNeighbourTerms.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullNumber_left_creator_neighbours", "fullNumber left creator neighbours", F4(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("fullNumber_right_creator_neighbours", "fullNumber right creator neighbours", F5(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-cubicproducts-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(Call("Fin", N("N")), N("Real")), All("j",
        Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("fullQ",
        N("coupling"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("fullSplit", N("j"))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("fullSplit", N("j"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("fullQ", N("coupling")))))), FormulaRelationOperator.Equal,
        Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("Fin", N("N")))), Parenthesized(Call("smul",
        Parenthesized(Seq(new Formula.Apply(N("coupling"), [N("i")]), Colon, N("Complex"))), Call("ite", new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("val", N("i"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))), FormulaRelationOperator.Equal, Call("val", N("j"))), new
        Formula.Binary(Parenthesized(Call("fullSplit", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))), Call("ite", new Formula.Logic(Parenthesized(new
        Formula.Relation(Call("val", N("i")), FormulaRelationOperator.Equal, Call("val", N("j")))),
        FormulaLogicOperator.Or, Parenthesized(new Formula.Relation(Call("val", N("i")),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("val", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(D(2)))))), new Formula.Binary(Parenthesized(Call("fullD", N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("fullSplit", N("j")))), Call("ite", new
        Formula.Relation(Call("val", N("i")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(3)))), new
        Formula.Binary(Parenthesized(Call("fullSplit", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))), D(0))))))))))))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), All("A", Call("FullOperator", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("symOp", N("N"), N("A")), Colon, Call("FullOperator", N("N")))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("A")), FormulaBinaryOperator.Add,
        Parenthesized(Call("adjoint", N("A"))))))));

    private static Formula F3() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(Call("Fin", N("N")), N("Real")), All("j",
        Call("Fin", N("N")), new Formula.Relation(Parenthesized(Seq(Call("creatorNeighbourTerms", N("N"),
        N("coupling"), N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Seq(Sum,
        Underscore, Grp(Seq(N("i"), InMacro, Call("Fin", N("N")))), Parenthesized(Call("ite", new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val", N("i"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, Call("val", N("j")))),
        FormulaLogicOperator.Or, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, Call("val",
        N("i"))))), Call("smul", Parenthesized(Seq(new Formula.Apply(N("coupling"), [N("i")]), Colon, N("Complex"))),
        new Formula.Binary(Parenthesized(Call("adjoint", Call("fullD", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i"))))), D(0)))))))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(Call("Fin", N("N")), N("Real")), All("k",
        Call("Fin", N("N")), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.Equal, Call("val", N("j")))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("creatorNeighbourTerms", N("coupling"), N("j")))), FormulaRelationOperator.Equal, Seq(Sum,
        Underscore, Grp(Seq(N("i"), InMacro, Call("Fin", N("N")))), Parenthesized(Call("ite", new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.Equal, Call("val", N("i"))), Call("smul", Parenthesized(Seq(new
        Formula.Apply(N("coupling"), [N("i")]), Colon, N("Complex"))), new
        Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullD", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i"))))))), D(0))))))))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(Call("Fin", N("N")), N("Real")), All("k",
        Call("Fin", N("N")), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.Equal, Call("val", N("k")))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("creatorNeighbourTerms", N("coupling"), N("j")))), FormulaRelationOperator.Equal, Seq(Sum,
        Underscore, Grp(Seq(N("i"), InMacro, Call("Fin", N("N")))), Parenthesized(Call("ite", new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("i"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.Equal, Call("val", N("j"))), Call("smul", Parenthesized(Seq(new
        Formula.Apply(N("coupling"), [N("i")]), Colon, N("Complex"))), new
        Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullD", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i"))))))), D(0))))))))))));
}
