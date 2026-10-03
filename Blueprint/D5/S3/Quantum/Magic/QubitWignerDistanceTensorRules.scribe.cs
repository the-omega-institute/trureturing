using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QubitWignerDistanceTensorRulesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dutta2026wignerdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Using the compact minimum bridge in WignerDistanceMinimum, equatorial qubit states obey exact multiplicativity of one plus the Wigner distance. Nonpositive Bloch-product states obey self-tensor superadditivity.",
        H("Tensor rules for the qubit Wigner distance"),
        Blocks(
            Definition("bloch", "Pauli expectation coordinates", BlochFormula(),
                "bloch(rho,p) is the real part of tr(rho pauliMatrix(p)). For p = X,Y,Z these are the Bloch coordinates r_x,r_y,r_z. Page 7: \"For a single-qubit state ρ with Bloch vector r⃗, write s(ρ) := sgn(r_x r_y r_z).\" The nonpositive sign condition is exactly r_x r_y r_z ≤ 0."),
            Definition("claimEquatorial", "Conjecture 5.6", Iff(V("claimEquatorial"), EquatorialFormula()),
                "Page 8, Conjecture 5.6 (Equatorial multiplicativity): \"For ⟨Z⟩_ρ = ⟨Z⟩_σ = 0: C(ρ ⊗ σ) = C(ρ) + C(σ) + C(ρ)C(σ).\" The quantifiers range over every complex two-by-two density matrix rho and sigma. IsDensity means positive semidefinite with trace one; the two Z expectations vanish separately. COne and CTwo denote WignerDistanceMinimum.COne and WignerDistanceMinimum.CTwo; COne_min and CTwo_min identify them with the source minimum on the corresponding Hilbert spaces."),
            Definition("claimSelfTensor", "Conjecture 5.7", Iff(V("claimSelfTensor"), SelfFormula()),
                "Page 8, Conjecture 5.7 (Self-tensor superadditivity, s ≤ 0 branch): \"For any qubit state ρ with s(ρ)≤ 0: C(ρ ⊗ ρ) ≥ 2C(ρ).\" Every density matrix is included, with the sign condition encoded by bloch(rho,X) bloch(rho,Y) bloch(rho,Z) ≤ 0. This includes zero coordinates and the stabilizer boundary."),
            Theorem("resultEquatorial", "Equatorial multiplicativity holds", V("claimEquatorial"),
                "Every qubit Wigner vector has at most one negative coordinate. On the nonpositive Bloch-product branch an explicit stabilizer-edge mixture has error ‖W‖₁−1. A product sign functional is bounded by one on every actual two-qubit stabilizer, using subgroup generators and an exact rational certificate on sixty candidate vectors. Convex weak duality gives the lower bound ‖W_rho‖₁ ‖W_sigma‖₁−1. The product of the two nearest mixtures gives the matching upper bound. Equatorial states lie on the zero Bloch-product branch."),
            Theorem("resultSelfTensor", "Self-tensor superadditivity holds", V("claimSelfTensor"),
                "On the nonpositive branch COne(rho) = ‖W_rho‖₁−1. Applying the same product dual bound to two copies of rho gives at least (1+COne(rho))²−1, which is at least 2 COne(rho). The free tensor mixture establishes nonemptiness of the two-qubit free set."))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create(name == "resultEquatorial"
                ? "dutta-tushar-2026-wigner-distance-equatorial-multiplicativity"
                : "dutta-tushar-2026-wigner-distance-self-tensor-superadditivity"), ResolutionKind.Proved));

    private static string NodeId(string name) => name switch
    {
        "PhasePoint" => "dutta-phase-carrier", "phasePoint" => "dutta-phase-operator",
        "phasePointTwo" => "dutta-product-frame", "Wigner" => "dutta-transform",
        "WignerOne" => "dutta-one-transform", "WignerTwo" => "dutta-two-transform",
        "pauliTwo" => "dutta-two-paulis",
        "Stab" => "dutta-stabilizers", "Wfree" => "dutta-free-polytope",
        "COne" => "dutta-one-distance", "CTwo" => "dutta-two-distance",
        "bloch" => "dutta-bloch", "claimEquatorial" => "dutta-equatorial-claim",
        "claimSelfTensor" => "dutta-self-claim", "resultEquatorial" => "dutta-equatorial-result",
        _ => "dutta-self-result"
    };
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Qubit() => V("QubitMatrix");
    private static Formula Tensor(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula TrRe(Formula m) => Call("re", Call("trace", m));
    private static Formula Pauli(string p) => V(p);
    private static Formula BlochFormula() => All("rho", Qubit(), All("p", V("Pauli"),
        Equal(Call("bloch", V("rho"), V("p")), TrRe(Multiply(V("rho"), Call("pauliMatrix", V("p")))))));
    private static Formula C(Formula rho) => Call("COne", rho);
    private static Formula EquatorialFormula()
    {
        var rho = V("rho"); var sigma = V("sigma");
        var conclusion = Equal(Call("CTwo", Tensor(rho, sigma)), Add(Add(C(rho), C(sigma)), Multiply(C(rho), C(sigma))));
        return All("rho", Qubit(), All("sigma", Qubit(), Imp(Call("IsDensity", rho), Imp(Call("IsDensity", sigma),
            Imp(Equal(Call("bloch", rho, Pauli("Z")), D(0)), Imp(Equal(Call("bloch", sigma, Pauli("Z")), D(0)), conclusion))))));
    }
    private static Formula SelfFormula()
    {
        var rho = V("rho");
        var product = Multiply(Multiply(Call("bloch", rho, Pauli("X")), Call("bloch", rho, Pauli("Y"))), Call("bloch", rho, Pauli("Z")));
        return All("rho", Qubit(), Imp(Call("IsDensity", rho), Imp(Rel(product, FormulaRelationOperator.LessThanOrEqual, D(0)),
            Rel(Call("CTwo", Tensor(rho, rho)), FormulaRelationOperator.GreaterThanOrEqual, Multiply(D(2), C(rho))))));
    }
}
