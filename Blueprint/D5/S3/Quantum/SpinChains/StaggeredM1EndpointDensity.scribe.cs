using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class StaggeredM1EndpointDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/beccaria2012staggered");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: StaggeredM1EndpointDensity"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("claim", "claim", F0(),
                "Section 3.2.3, printed page 13: “As similar pattern is found by probing if a particle is present on the last site. The data is consistent with ρ_n^{(N)}(y) = y^{−2} ρ_n^{(1)}(y) for finite n ≤ 8. We conjecture this to hold for arbitrary system sizes.” Here N = 3n with n ≥ 1, y is real and nonzero, and density(j,psi) is the normalized occupation expectation at the one-based site j. The claim quantifies over every nonzero zero-energy state; it contains the source ground-state assertion without assuming existence or uniqueness.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", F1(),
                "The period-three identity for R has expectation zero in every zero-energy state, since Q and its Hilbert adjoint both annihilate that state. With couplings (y,y,1) the remaining boundary term gives density(N,psi)=y⁻² density(1,psi). The argument holds for every nonzero zero-energy state and does not prove its existence or uniqueness.", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("beccaria-hagendorf-2012-staggered-m1-endpoint-density"),
                    ResolutionKind.Proved)))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("m1-staggeredm1endpointdensity-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(new Formula.Relation(Parenthesized(Seq(Call("claim"), Colon, N("Prop"))), FormulaRelationOperator.Equal,
        All("n", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(All("y",
        N("Real"), new Formula.Logic(Parenthesized(new Formula.Relation(N("y"), FormulaRelationOperator.NotEqual,
        D(0))), FormulaLogicOperator.Implies, Parenthesized(All("psi", Call("HardCoreSpace", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n")))), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("psi"), FormulaRelationOperator.NotEqual, D(0))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("H", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n"))), Call("stagII",
        N("y")), N("psi")), FormulaRelationOperator.Equal, D(0))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(Call("density", new Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("n"))), N("psi")), FormulaRelationOperator.Equal, Call("smul", Call("asReal", new
        Formula.Power(Parenthesized(Call("inv", N("y"))), D(2))), Call("density", D(1), N("psi")))))))))))))))));

    private static Formula F1() =>
        Disp(All("n", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(All("y",
        N("Real"), new Formula.Logic(Parenthesized(new Formula.Relation(N("y"), FormulaRelationOperator.NotEqual,
        D(0))), FormulaLogicOperator.Implies, Parenthesized(All("psi", Call("HardCoreSpace", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n")))), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("psi"), FormulaRelationOperator.NotEqual, D(0))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("H", new
        Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply, Parenthesized(N("n"))), Call("stagII",
        N("y")), N("psi")), FormulaRelationOperator.Equal, D(0))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(Call("density", new Formula.Binary(Parenthesized(D(3)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("n"))), N("psi")), FormulaRelationOperator.Equal, Call("smul", Call("asReal", new
        Formula.Power(Parenthesized(Call("inv", N("y"))), D(2))), Call("density", D(1), N("psi"))))))))))))))));
}
