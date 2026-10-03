using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class HardCoreCompressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: HardCoreCompression"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("fullD_hardCore_iff", "fullD hardCore iff", F2(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("restrictOp_fullD", "restrictOp fullD", F5(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("restrictOp_fullNumber", "restrictOp fullNumber", F6(),
                "The displayed identity is obtained by the occupation-basis calculation, retaining the fermionic signs and the finite-chain boundary cases.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-hardcorecompression-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F2() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), All("s", Call("Assignment", N("N")), All("t",
        Call("Assignment", N("N")), new Formula.Logic(Parenthesized(new Formula.Relation(Call("fullD", N("i"), N("s"),
        N("t")), FormulaRelationOperator.NotEqual, D(0))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(Call("Adm", N("N"), N("s"))), FormulaLogicOperator.Iff,
        Parenthesized(Call("Adm", N("N"), N("t")))))))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new Formula.Relation(Call("submatrix", Call("fullD",
        N("i")), Call("Subtypeval"), Call("Subtypeval")), FormulaRelationOperator.Equal, Call("annihilationAt", N("i"))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new Formula.Relation(Call("submatrix", Call("boolReindex", Call("localOp", N("i"), Call("finTwoReindex", Call("visibleProjector")))), Call("Subtypeval"), Call("Subtypeval")), FormulaRelationOperator.Equal, Call("number", new
        Formula.Binary(Parenthesized(Call("val", N("i"))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))));
}
