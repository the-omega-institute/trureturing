using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class JordanWignerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/beccaria2012staggered");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: JordanWigner"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("Local", "Local", F0(),
                "The displayed equation defines Local.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("FullOperator", "FullOperator", F1(),
                "The displayed equation defines FullOperator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fermionWord", "fermionWord", F3(),
                "The displayed equation defines fermionWord.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullC", "fullC", F4(),
                "The displayed equation defines fullC.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("prefixCount", "prefixCount", F5(),
                "The displayed equation defines prefixCount.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fullC_anticomm_of_lt", "fullC anticomm of lt", F6(),
                "Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("fullC_CAR", "fullC CAR", F7(),
                "Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("fullC_mixed_anticomm_of_lt", "fullC mixed anticomm of lt", F8(),
                "Section 2.1, printed page 2, states the canonical fermionic anticommutation rules. The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-jordanwigner-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(new Formula.Relation(Parenthesized(Seq(Call("Local"), Colon, N("Type"))), FormulaRelationOperator.Equal,
        Call("Matrix", N("Bool"), N("Bool"), N("Complex"))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("FullOperator", N("N")), Colon,
        N("Type"))), FormulaRelationOperator.Equal, Call("Matrix", Call("Assignment", N("N")), Call("Assignment",
        N("N")), N("Complex")))));

    private static Formula F3() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), All("i", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("fermionWord", N("N"), N("j"), N("i")), Colon, Call("Local"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(N("i"), FormulaRelationOperator.LessThan,
        N("j")), N("spinZ"), Call("ite", new Formula.Relation(N("i"), FormulaRelationOperator.Equal, N("j")),
        Call("Matrixsingle", N("false"), N("true"), Parenthesized(Seq(D(1), Colon, N("Complex")))), D(1))))))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("j", Call("Fin", N("N")), new Formula.Relation(Parenthesized(Seq(Call("fullC",
        N("N"), N("j")), Colon, Call("FullOperator", N("N")))), FormulaRelationOperator.Equal, Call("tensorOp",
        Call("fermionWord", N("j")))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("t", Call("Assignment", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("prefixCount", N("N"), N("t"), N("j")), Colon, N("Nat"))), FormulaRelationOperator.Equal,
        Call("card", Call("Finsetunivfilter", Seq(N("i"), Colon, Call("Fin", N("N")), Mapsto, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.LessThan, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(new Formula.Apply(N("t"), [N("i")]),
        FormulaRelationOperator.Equal, N("true")))))))))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.LessThan, N("j"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullC", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullC", N("j"))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullC", N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullC", N("i")))))), FormulaRelationOperator.Equal, D(0))))))));

    private static Formula F7() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new Formula.Relation(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("fullC", N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("fullC", N("i")))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("adjoint", Call("fullC",
        N("i")))), FormulaBinaryOperator.Multiply, Parenthesized(Call("fullC", N("i")))))),
        FormulaRelationOperator.Equal, Parenthesized(Seq(D(1), Colon, Call("FullOperator", N("N"))))))));

    private static Formula F8() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("j", Call("Fin", N("N")), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.LessThan, N("j"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("fullC", N("i"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("fullC", N("j")))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("adjoint", Call("fullC", N("j")))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("fullC", N("i")))))), FormulaRelationOperator.Equal, D(0))))))));
}
