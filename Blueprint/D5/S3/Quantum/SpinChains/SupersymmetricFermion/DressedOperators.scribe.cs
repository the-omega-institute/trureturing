using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class DressedOperatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: DressedOperators"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("dressedWord", "dressedWord", F0(),
                "The displayed equation defines dressedWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullD", "fullD", F1(),
                "The displayed equation defines fullD.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullD_far_mixed_anticomm", "fullD far mixed anticomm", F2(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("fullD_far_anticomm", "fullD far anticomm", F3(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("neighbourPWord", "neighbourPWord", F4(),
                "The displayed equation defines neighbourPWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullD_CAR", "fullD CAR", F5(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("splitWord", "splitWord", F6(),
                "The displayed equation defines splitWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullSplit", "fullSplit", F7(),
                "The displayed equation defines fullSplit.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullD_before_split_anticomm", "fullD before split anticomm", F8(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("numberWord", "numberWord", F9(),
                "The displayed equation defines numberWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullD_number_same", "fullD number same", F11(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("fullD_number_commute", "fullD number commute", F12(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-dressedoperators-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), All("i", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("dressedWord", N("N"), N("j"), N("i")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("i"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, Call("val",
        N("j"))), N("spinP"), Call("ite", new Formula.Relation(N("i"), FormulaRelationOperator.LessThan, N("j")),
        N("spinZ"), Call("ite", new Formula.Relation(N("i"), FormulaRelationOperator.Equal, N("j")), Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))),
        Call("ite", new Formula.Relation(Call("val", N("i")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        N("spinP"), D(1))))))))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Relation(Parenthesized(Seq(Call("fullD",
        N("N"), N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("tensorOp",
        Call("dressedWord", N("j")))))));

    private static Formula F2() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val", N("i"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.LessThan, Call("val", N("j")))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullD", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("fullD", N("j")))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullD", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))))), FormulaRelationOperator.Equal, D(0))))))));

    private static Formula F3() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val", N("i"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.LessThan, Call("val", N("j")))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullD", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("j"))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullD", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))))), FormulaRelationOperator.Equal, D(0))))))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), All("k", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("neighbourPWord", N("N"), N("j"), N("k")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.Equal, Call("val", N("j")))), FormulaLogicOperator.Or, Parenthesized(new
        Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        N("spinP"), D(1)))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new Formula.Relation(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("fullD", N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("fullD", N("i")))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("adjoint", Call("fullD",
        N("i")))), FormulaBinaryOperator.Multiply, Parenthesized(Call("fullD", N("i")))))),
        FormulaRelationOperator.Equal, Call("tensorOp", Call("neighbourPWord", N("i")))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), All("k", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("splitWord", N("N"), N("j"), N("k")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, Call("val",
        N("j"))), N("spinP"), Call("ite", new Formula.Relation(N("k"), FormulaRelationOperator.LessThan, N("j")),
        N("spinZ"), Call("ite", new Formula.Relation(N("k"), FormulaRelationOperator.Equal, N("j")), Call("adjoint",
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex"))))), Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))), Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2)))),
        Call("adjoint", Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex"))))), Call("ite", new Formula.Relation(Call("val", N("k")),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("val", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(D(3)))), N("spinP"), D(1))))))))))));

    private static Formula F7() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Relation(Parenthesized(Seq(Call("fullSplit",
        N("N"), N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("tensorOp",
        Call("splitWord", N("j")))))));

    private static Formula F8() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val", N("i"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.LessThan, Call("val", N("j")))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullD", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullSplit", N("j"))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullSplit", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))))), FormulaRelationOperator.Equal, D(0))))))));

    private static Formula F9() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("k", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("numberWord", N("N"), N("i"), N("k")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(N("k"), FormulaRelationOperator.Equal,
        N("i")), new Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(N("spinP"))),
        D(1)))))));

    private static Formula F11() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("fullD", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("boolReindex", Call("localOp", N("i"), Call("finTwoReindex", Call("visibleProjector")))))), FormulaRelationOperator.Equal, Call("fullD", N("i")))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("i"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))), FormulaRelationOperator.Equal, D(0)))))));

    private static Formula F12() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.NotEqual, N("j"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("fullD", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("boolReindex", Call("localOp", N("j"), Call("finTwoReindex", Call("visibleProjector")))))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("j"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", N("i")))))))))));
}
