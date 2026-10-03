using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class HoppingProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: HoppingProducts"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("fullPAt", "fullPAt", F0(),
                "The displayed equation defines fullPAt.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullLeftP", "fullLeftP", F1(),
                "The displayed equation defines fullLeftP.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("hopWord", "hopWord", F2(),
                "The displayed equation defines hopWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullHop", "fullHop", F3(),
                "The displayed equation defines fullHop.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fourHopWord", "fourHopWord", F4(),
                "The displayed equation defines fourHopWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullFourHop", "fullFourHop", F5(),
                "The displayed equation defines fullFourHop.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("hop_dressed", "hop dressed", F6(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("split_at_left", "split at left", F7(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("split_at_right", "split at right", F8(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("split_before", "split before", F9(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("split_after", "split after", F10(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("fullHop_PAt_commute", "fullHop PAt commute", F11(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("fullOccupationAt", "fullOccupationAt", F12(),
                "The displayed equation defines fullOccupationAt.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-hoppingproducts-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("fullPAt", N("N"),
        N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("tensorOp", Seq(N("k"),
        Colon, Call("Fin", N("N")), Mapsto, Parenthesized(Call("ite", new Formula.Relation(Call("val", N("k")),
        FormulaRelationOperator.Equal, N("j")), N("spinP"), D(1)))))))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("fullLeftP", N("N"),
        N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("tensorOp", Seq(N("k"),
        Colon, Call("Fin", N("N")), Mapsto, Parenthesized(Call("ite", new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.Equal, N("j")), N("spinP"), D(1)))))))));

    private static Formula F2() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("k", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("hopWord", N("N"), N("j"), N("k")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, N("j")), N("spinP"),
        Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, N("j")), Call("adjoint",
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex"))))), Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))),
        Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(2)))), N("spinP"),
        D(1))))))))));

    private static Formula F3() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("fullHop", N("N"),
        N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("ite", new
        Formula.Relation(new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.LessThan, N("N")), Call("tensorOp", Call("hopWord", N("j"))), D(0))))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("k", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("fourHopWord", N("N"), N("j"), N("k")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(new Formula.Binary(Parenthesized(Call("val",
        N("k"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.Equal, N("j")), N("spinP"),
        Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, N("j")), Call("adjoint",
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex"))))), Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))),
        Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(2)))), Call("adjoint",
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex"))))), Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(3)))), Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))),
        Call("ite", new Formula.Relation(Call("val", N("k")), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(4)))), N("spinP"),
        D(1))))))))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("fullFourHop", N("N"),
        N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("ite", new
        Formula.Relation(new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(3))),
        FormulaRelationOperator.LessThan, N("N")), Call("tensorOp", Call("fourHopWord", N("j"))), D(0))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(Call("fullHop", N("N"), Call("val", N("j"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullD", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", Parenthesized(Seq(Call("mk", new Formula.Binary(Parenthesized(Call("val",
        N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), Colon, Call("Fin", N("N")))))))))))));

    private static Formula F7() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("fullD", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullSplit", N("j")))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullHop", N("N"), new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("fullLeftP", N("N"), Call("val", N("j")))))))))));

    private static Formula F8() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("fullD", Parenthesized(Seq(Call("mk", new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2)))), Colon,
        Call("Fin", N("N")))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("fullSplit", N("j")))),
        FormulaRelationOperator.Equal, new Formula.Negate(new Formula.Binary(Parenthesized(Call("fullHop", N("N"),
        Call("val", N("j")))), FormulaBinaryOperator.Multiply, Parenthesized(Call("fullPAt", N("N"), new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(3)))))))))))));

    private static Formula F9() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(2))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("val",
        N("j")))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("fullSplit", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", Parenthesized(Seq(Call("mk", new Formula.Binary(Parenthesized(Call("val",
        N("j"))), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))), Colon, Call("Fin", N("N"))))))),
        FormulaRelationOperator.Equal, Call("adjoint", Call("fullFourHop", N("N"), new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))))))))));

    private static Formula F10() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(3))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(Call("fullSplit", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullD", Parenthesized(Seq(Call("mk", new Formula.Binary(Parenthesized(Call("val",
        N("j"))), FormulaBinaryOperator.Add, Parenthesized(D(3)))), Colon, Call("Fin", N("N"))))))),
        FormulaRelationOperator.Equal, new Formula.Negate(Call("fullFourHop", N("N"), Call("val", N("j"))))))))));

    private static Formula F11() =>
        Disp(All("N", N("Nat"), All("h", N("Nat"), All("k", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(N("k"), FormulaRelationOperator.NotEqual, N("h"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("k"), FormulaRelationOperator.NotEqual,
        new Formula.Binary(Parenthesized(N("h")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("fullHop", N("N"), N("h"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullPAt", N("N"), N("k")))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("fullPAt", N("N"), N("k"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullHop", N("N"), N("h")))))))))))));

    private static Formula F12() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("fullOccupationAt",
        N("N"), N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(Call("fullPAt", N("N"),
        N("j"))))))));
}
