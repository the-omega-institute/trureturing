using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class WassersteinComplexityNonconvexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/bunthpitriktitkosvirosztek2024wasserstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qubit dephasing midpoint refutes convexity of Wasserstein complexity.",
        H("WassersteinComplexityNonconvex"),
        Blocks(
            Node("trace_sqrt_sq_le_two", Disp(All("rho", Mat(D(2)), Imp(QC("CoPRelativeQuantumnessRefutation", "IsDensity", V("rho")), LeqF(new Formula.Power(QC("Complex", "re", QC("Matrix", "trace", QC("CFC", "sqrt", V("rho")))), D(2)), D(2))))), "For every two-dimensional density matrix, the square of the real trace of its positive square root is at most two.", AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("pure_diag_coupling", Disp(All("omega", Mat(D(2)), All("P", C("Matrix", Parenthesized(Seq(FinF(D(2)), Sp, Times, Sp, FinF(D(2)))), Parenthesized(Seq(FinF(D(2)), Sp, Times, Sp, FinF(D(2)))), ComplexF()), Imp(new Formula.Relation(V("P"), FormulaRelationOperator.MemberOf, QC("QubitWassersteinCouplings", "couplings", QC("ProjectedUnistochasticDynamics", "diagonalState", Vector(D(1), D(0))), V("omega"))), Eqn(V("P"), QC("Matrix", "kronecker", V("omega"), QC("Matrix", "transpose", QC("ProjectedUnistochasticDynamics", "diagonalState", Vector(D(1), D(0)))))))))), "A coupling whose prescribed transposed marginal is the pure zero state factors as the other marginal tensor that pure state.", AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("claim", Disp(IffF(C("claim"), ClaimBody())), "Source §5.1, PDF p. 18, verbatim: “We note that whether the Wasserstein complexity (37) is convex or not is an open question.” This is the universal convexity question for every finite dimension and finite Hermitian observable family, CPTP endpoints and a real mixture weight in [0,1]. The literal d=0 case is retained.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("phaseU", Disp(All("e", Real(), Eqn(C("phaseU", V("e")), QC("Matrix", "diagonal", Vector(Div(Add(QC("Complex", "ofReal", Root(D(3))), Mul(QC("Complex", "ofReal", V("e")), QC("Complex", "I"))), D(2)), Div(Sub(QC("Complex", "ofReal", Root(D(3))), Mul(QC("Complex", "ofReal", V("e")), QC("Complex", "I"))), D(2))))))), "At the dephasing parameter t=1/4 the phase matrices are diagonal with entries (sqrt 3 plus or minus i e)/2.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("Phi", Disp(All("e", Real(), All("rho", Mat(D(2)), Eqn(C("Phi", V("e"), V("rho")), Evolution(C("phaseU", V("e")), V("rho")))))), "Phi e is the complex-linear conjugation map by phaseU e; the endpoints have e=1 and e=-1.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("AdZ", Disp(All("rho", Mat(D(2)), Eqn(C("AdZ", V("rho")), Mul(Mul(QC("FiniteDimensional", "qubitZ"), V("rho")), QC("FiniteDimensional", "qubitZ"))))), "AdZ is the complex-linear conjugation map by the frozen qubitZ.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("Psi", Disp(Eqn(C("Psi"), Add(Smul(Div(D(3), D(4)), QC("LinearMap", "id")), Smul(Div(D(1), D(4)), C("AdZ"))))), "Psi is the identity/dephasing mixture with t=1/4. The endpoint channel mixture weight is s=1/2.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("result", Disp(NotF(Parenthesized(ClaimBody()))), "For the channels Φ₊ and Φ₋ at t=1/4 and their midpoint Ψ at s=1/2, the endpoint bound is C_W(Φ₊), C_W(Φ₋) ≤ √2 while C_W(Ψ) ≥ √(1+√3), with √(1+√3) > √2, so the midpoint value is strictly larger than the endpoint bound.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("qwc-" + name.Replace("_", "").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimBody() => All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), Imp(All("j", FinF(V("k")), QC("Matrix", "IsHermitian", Apply(V("A"), V("j")))), All("Phi1", Maps(V("d")), All("Phi2", Maps(V("d")), Imp(QC("CoPRelativeQuantumnessRefutation", "IsCPTP", V("Phi1")), Imp(QC("CoPRelativeQuantumnessRefutation", "IsCPTP", V("Phi2")), All("s", Real(), Imp(LeqF(D(0), V("s")), Imp(LeqF(V("s"), D(1)), LeqF(C("CW", V("A"), Add(Smul(V("s"), V("Phi1")), Smul(Sub(D(1), V("s")), V("Phi2")))), Add(Mul(V("s"), C("CW", V("A"), V("Phi1"))), Mul(Sub(D(1), V("s")), C("CW", V("A"), V("Phi2"))))))))))))))));

    private static Formula NotF(Formula value) => new Formula.Not(value);
    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(FormulaDsl.Id(owner)), Dot, Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(FormulaDsl.Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(FormulaDsl.Id(name))), [.. args]);
    private static Formula QC(string owner, string name, params Formula[] args) => args.Length == 0 ? Q(owner, name) : new Formula.Apply(Q(owner, name), [.. args]);
    private static Formula Apply(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqF(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffF(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Nat() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula ComplexF() => Seq(Mathbb, Grp(FormulaDsl.Id("C")));
    private static Formula FinF(Formula size) => C("Fin", size);
    private static Formula Mat(Formula size) => C("Matrix", FinF(size), FinF(size), ComplexF());
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Maps(Formula size) => C("LinearMap", ComplexF(), Mat(size), Mat(size));
    private static Formula Root(Formula value) => QC("Real", "sqrt", value);
    private static Formula Evolution(Formula u, Formula rho) => QC("ProjectedUnistochasticDynamics", "unitaryEvolution", u, rho);
    private static Formula Vector(params Formula[] items) => Seq(Bang, OpenBracket, VectorItems(items), CloseBracket);
    private static Formula VectorItems(Formula[] items) => items.Length == 2 ? Seq(items[0], Comma, Sp, items[1]) : Seq(items[0], Comma, Sp, items[1], Comma, Sp, items[2]);
}
