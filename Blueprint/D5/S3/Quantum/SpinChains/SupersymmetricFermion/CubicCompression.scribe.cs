using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class CubicCompressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicCompression.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: CubicCompression"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("fullR", "fullR", F0(),
                "The displayed equation defines fullR.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("HCBlock", "HCBlock", F1(),
                "The displayed equation defines HCBlock.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("HCBlock_fullNumber", "HCBlock fullNumber", F2(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("chainG", "chainG", F3(),
                "The displayed equation defines chainG.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("blockR", "blockR", F4(),
                "The displayed equation defines blockR.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("blockDiagonal", "blockDiagonal", F5(),
                "The displayed equation defines blockDiagonal.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("hopCurrent", "hopCurrent", F6(),
                "The displayed equation defines hopCurrent.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fourCurrent", "fourCurrent", F7(),
                "The displayed equation defines fourCurrent.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bulkCurrent", "bulkCurrent", F8(),
                "The displayed equation defines bulkCurrent.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullBoundary", "fullBoundary", F9(),
                "The displayed equation defines fullBoundary.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("w", "w", F10(),
                "The displayed equation defines w.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("occReal", "occReal", F11(),
                "The displayed equation defines occReal.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("diagonalCoefficient", "diagonalCoefficient", F12(),
                "The displayed equation defines diagonalCoefficient.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-cubiccompression-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), new
        Formula.Relation(Parenthesized(Seq(Call("fullR", N("N"), N("a"), N("b"), N("cc")), Colon, Call("FullOperator",
        N("N")))), FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(D(0),
        FormulaRelationOperator.LessThan, N("N")), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(N("cc")), D(2))))), Call("adjoint", Call("fullD", Parenthesized(Seq(Call("mk",
        D(0)), Colon, Call("Fin", N("N")))))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("a")), D(2))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("cc")))), Call("adjoint", Call("fullD",
        Parenthesized(Seq(Call("mk", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))), Colon, Call("Fin", N("N")))))))))), FormulaBinaryOperator.Add, Parenthesized(Seq(Sum,
        Underscore, Grp(Seq(N("k"), InMacro, Call("Fin", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))), Parenthesized(Call("smul", Call("asReal", new
        Formula.Binary(Parenthesized(Call("periodThree", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(3))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("periodThree", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(2))))), D(2))))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", Parenthesized(Seq(Call("mk", Call("val", N("k"))), Colon, Call("Fin", N("N")))), Call("finTwoReindex", Call("visibleProjector"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("fullD", Parenthesized(Seq(Call("mk", new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2)))), Colon,
        Call("Fin", N("N")))))))))))))), FormulaBinaryOperator.Subtract, Parenthesized(Seq(Sum, Underscore,
        Grp(Seq(N("k"), InMacro, Call("Fin", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))))), Parenthesized(Call("smul", Call("asReal", new
        Formula.Binary(Parenthesized(Call("periodThree", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("periodThree", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(2))))), D(2))))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", Parenthesized(Seq(Call("mk", new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(2)))), Colon, Call("Fin", N("N")))), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("fullD", Parenthesized(Seq(Call("mk", Call("val", N("k"))), Colon,
        Call("Fin", N("N")))))))))))))), FormulaBinaryOperator.Add, Parenthesized(Call("smul", Call("asReal", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply,
        Parenthesized(N("b")))), FormulaBinaryOperator.Multiply, Parenthesized(N("cc")))), Seq(Sum, Underscore,
        Grp(Seq(N("k"), InMacro, Call("Fin", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))))), Parenthesized(Call("fullSplit", Parenthesized(Seq(Call("mk", Call("val", N("k"))),
        Colon, Call("Fin", N("N")))))))))), D(0))))))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), All("A", Call("FullOperator", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("HCBlock", N("N"), N("A")), Colon, N("Prop"))),
        FormulaRelationOperator.Equal, All("s", Call("Assignment", N("N")), All("t", Call("Assignment", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(N("A"), [N("s"), N("t")]),
        FormulaRelationOperator.NotEqual, D(0))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(Call("Adm", N("N"), N("s"))), FormulaLogicOperator.Iff,
        Parenthesized(Call("Adm", N("N"), N("t"))))))))))));

    private static Formula F2() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), Call("HCBlock", Call("boolReindex", Call("localOp", N("i"), Call("finTwoReindex", Call("visibleProjector"))))))));

    private static Formula F3() =>
        Disp(All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Call("asReal", Call("chainG", N("a"), N("b"), N("cc"), N("j"))),
        FormulaRelationOperator.Equal, Call("periodThree", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("k", Call("Fin",
        N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2))), FormulaRelationOperator.LessThan, N("N"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Parenthesized(Seq(Call("blockR", N("N"),
        N("a"), N("b"), N("cc"), N("k")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, new
        Formula.Apply(Parenthesized(Seq(N("j"), Colon, Call("Fin", N("N")), Mapsto, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal",
        new Formula.Binary(Parenthesized(Call("chainG", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"), N("b"),
        N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), D(2))))), Colon, N("Complex"))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("fullD", N("j"))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal", new
        Formula.Binary(Parenthesized(Call("chainG", N("a"), N("b"), N("cc"), Call("val", N("k")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"), N("b"),
        N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), D(2))))), Colon, N("Complex"))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("j"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("fullD", N("k"))))))))),
        FormulaBinaryOperator.Add, Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply,
        Parenthesized(N("b")))), FormulaBinaryOperator.Multiply, Parenthesized(N("cc")))), Colon, N("Complex"))),
        Call("fullSplit", N("k")))))))), [Call("mk", new Formula.Binary(Parenthesized(Call("val", N("k"))),
        FormulaBinaryOperator.Add, Parenthesized(D(2))))]))))))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("k", Call("Fin",
        N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2))), FormulaRelationOperator.LessThan, N("N"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Parenthesized(Seq(Call("blockDiagonal",
        N("N"), N("a"), N("b"), N("cc"), N("k")), Colon, Call("FullOperator", N("N")))),
        FormulaRelationOperator.Equal, new Formula.Apply(Parenthesized(Seq(N("j"), Colon, Call("Fin", N("N")), Mapsto,
        Parenthesized(new Formula.Binary(Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(2))))),
        D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), D(2))))), Colon, N("Complex"))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("k"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("tensorOp", Call("neighbourPWord", N("j"))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"), N("b"), N("cc"), Call("val", N("k")))),
        D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("chainG", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), D(2))))), Colon, N("Complex"))), new Formula.Binary(Parenthesized(Call("boolReindex", Call("localOp", N("j"), Call("finTwoReindex", Call("visibleProjector"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("tensorOp", Call("neighbourPWord",
        N("k"))))))))))), [Call("mk", new Formula.Binary(Parenthesized(Call("val", N("k"))),
        FormulaBinaryOperator.Add, Parenthesized(D(2))))]))))))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("hopCurrent", N("N"), N("a"), N("b"), N("cc"), N("j")), Colon,
        Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("smul", Parenthesized(Seq(Call("chainG",
        N("a"), N("b"), N("cc"), new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add,
        Parenthesized(D(2)))), Colon, N("Complex"))), Call("symOp", Call("fullHop", N("N"), N("j")))))))))));

    private static Formula F7() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("fourCurrent", N("N"), N("a"), N("b"), N("cc"), N("j")), Colon,
        Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("smul", Parenthesized(Seq(Call("chainG",
        N("a"), N("b"), N("cc"), new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add,
        Parenthesized(D(3)))), Colon, N("Complex"))), Call("symOp", Call("fullFourHop", N("N"), N("j")))))))))));

    private static Formula F8() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("bulkCurrent", N("N"), N("a"), N("b"), N("cc"), N("j")), Colon,
        Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, new Formula.Apply(Parenthesized(Seq(N("C"),
        Mapsto, Parenthesized(new Formula.Apply(Parenthesized(Seq(N("x"), Mapsto, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Apply(N("C"), [new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))])), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(Call("ite", new
        Formula.Relation(N("j"), FormulaRelationOperator.Equal, D(0)), D(0), new Formula.Apply(N("x"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))]))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("C"),
        [N("j")])), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(D(1)),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("x"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(3)))])))))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("C"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(2)))])),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Apply(N("x"), [N("j")])))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(Call("ite", new
        Formula.Relation(N("j"), FormulaRelationOperator.Equal, D(0)), D(0), new Formula.Apply(N("C"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))]))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Apply(N("x"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(2)))])))))))),
        [Call("fullOccupationAt", N("N"))])))), [Call("hopCurrent", N("N"), N("a"), N("b"), N("cc"))]))))))));

    private static Formula F9() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), new
        Formula.Relation(Parenthesized(Seq(Call("fullBoundary", N("N"), N("a"), N("b"), N("cc")), Colon,
        Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(D(0),
        FormulaRelationOperator.LessThan, N("N")), new Formula.Binary(Parenthesized(Call("smul",
        Parenthesized(Seq(Call("asReal", new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Power(Parenthesized(N("cc")), D(2))))), Colon, N("Complex"))), Call("adjoint",
        Call("fullD", Parenthesized(Seq(Call("mk", D(0)), Colon, Call("Fin", N("N")))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("smul", Parenthesized(Seq(Call("asReal", new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("a")), D(2))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("cc")))), Colon, N("Complex"))), Call("adjoint", Call("fullD", Parenthesized(Seq(Call("mk",
        new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))), Colon,
        Call("Fin", N("N"))))))))), D(0))))))));

    private static Formula F10() =>
        Disp(All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Call("asReal", Call("w", N("a"), N("b"), N("cc"), N("j"))), FormulaRelationOperator.Equal,
        new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("periodThree", N("a"), N("b"), N("cc"),
        new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))))), D(2))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("periodThree", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(2))))),
        D(2))))))))));

    private static Formula F11() =>
        Disp(All("N", N("Nat"), All("s", Call("HardCore", N("N")), All("j", N("Nat"), new
        Formula.Relation(Call("asReal", Call("occReal", N("N"), N("s"), N("j"))), FormulaRelationOperator.Equal,
        Call("ite", Call("occupied", Call("val", N("s")), N("j")), D(1), D(0)))))));

    private static Formula F12() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("s", Call("HardCore",
        N("N")), new Formula.Relation(Call("asReal", Call("diagonalCoefficient", N("N"), N("a"), N("b"), N("cc"),
        N("s"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("a")), D(2))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Power(Parenthesized(N("cc")), D(2))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(Call("occReal", N("s"), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("occReal", N("s"), D(2))))))), FormulaBinaryOperator.Add,
        Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("Finsetrange", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))),
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("w", N("a"), N("b"), N("cc"), new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("occReal", N("s"), new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(Call("occReal", N("s"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(4))))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("w", N("a"), N("b"), N("cc"), new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(3))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("occReal", N("s"), new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(3))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(Call("occReal", N("s"),
        N("i")))))))))))))))))));
}
