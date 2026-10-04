using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GHZMeasureBiseparableBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/wuzhongwu2026ghzmeasure");
    private const string SpinQuote = "For a unit vector n⃗ ∈ R³, the spin observable on a single qubit is σ_n⃗ = n⃗ · σ = n_x σ_x + n_y σ_y + n_z σ_z, with σ_x, σ_y, σ_z the standard Pauli matrices. For three direction labels n⃗_a, n⃗_b, n⃗_c we denote the tripartite local observable σ(n⃗_a, n⃗_b, n⃗_c) = σ_n⃗_a ⊗ σ_n⃗_b ⊗ σ_n⃗_c, (1) and its expectation ⟨σ(n⃗_a, n⃗_b, n⃗_c)⟩ = Tr[σ(n⃗_a, n⃗_b, n⃗_c)ρ_ABC].";
    private const string IstarQuote = "The fix is to allow each party its own orthonormal frame. Let (â₁, â₂), (b̂₁, b̂₂), (ĉ₁, ĉ₂) be orthonormal pairs on A, B, C, and set I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ) = ⟨σ_â₁ σ_b̂₁ σ_ĉ₁⟩ − ⟨σ_â₁ σ_b̂₂ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₁ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₂ σ_ĉ₁⟩, (27) the natural independent-frame analogue of (2) (here σ_â σ_b̂ σ_ĉ abbreviates σ_â ⊗ σ_b̂ ⊗ σ_ĉ).";
    private const string MeasureQuote = "Define the local-unitary invariant measure E_GHZ(ρ) = ½ sup_{â₁⊥â₂, b̂₁⊥b̂₂, ĉ₁⊥ĉ₂} |I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ)|. (30)";
    private const string ClaimQuote = "Numerically maximising E_GHZ over all biseparable A|BC states we find the sharp value sup_{ρ ∈ A|BC} E_GHZ(ρ) = ½, (37) attained e.g. by |0⟩_A ⊗ |Φ⁺⟩_BC and coinciding with the product-state value (34); the analytic proof of the exact constant 1/2 remains open. The same 1/2 holds for the B|AC and C|AB partitions by symmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The GHZ measure has sharp bound one half on arbitrary A|BC product density states.",
        H("The sharp A|BC constant of the GHZ measure"),
        Blocks(
            Paragraph(Text("Fin k denotes the k computational labels, indexed from zero. QubitMatrix is Matrix (Fin 2) (Fin 2) Complex and TwoQubitMatrix is Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Complex. The three-qubit matrix index is Fin 2 × (Fin 2 × Fin 2). Real triples use the Euclidean dotProduct(a,b) = sum over i : Fin 3 of a(i)b(i), not the supremum norm of functions. toLp(2,a) puts the coordinates a into EuclideanSpace Real (Fin 3); vecCons(a,vecCons(b,vecEmpty)) is the two-vector family indexed by Fin 2. Orthonormal Real requires both squared Euclidean lengths to be one and their dot product to vanish. blochMatrix is D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix; at trace parameter zero and coordinates toLp(2, fun i => 2*n(i)), it has entries n(2), n(0) - I*n(1), n(0) + I*n(1), -n(2), read by rows, the Pauli spin expression in equation (1). The symbols a1,a2,b1,b2,c1,c2 represent Lean's subscripted direction names. ofReal explicitly embeds a real scalar into Complex, smul is scalar multiplication, kronecker is Matrix.kroneckerMap with scalar multiplication, trace is the complex matrix trace, re is the real part and sSup is the real supremum. Anonymous square brackets display Lean typeclass assumptions. All formulas bind every parameter; fixed imported operators are named constants.")),
            Node("IsDensity", "Arbitrary density matrices", DensityFormula(),
                "A density matrix is positive semidefinite with complex trace one. The finite index type n is arbitrary, so both single-qubit and two-qubit mixed states are included."),
            Node("expect", "Real trace expectation", ExpectFormula(),
                "Section I, printed page 2: “" + SpinQuote + "” The real part is explicit in Lean; for the Hermitian observables and density matrices in the bound, the imaginary part is zero."),
            Node("observable", "The three-qubit tensor observable", ObservableFormula(),
                "Section I, printed page 2, equation (1): “" + SpinQuote + "” The tensor is associated as A tensor (B tensor C), retaining all three independent directions."),
            Node("E", "Three-body correlation", CorrelationFormula(),
                "The expectation of the observable in equation (1), with the real part written explicitly."),
            Node("Istar", "The independent-frame functional", IstarFormula(),
                "Section V.B, printed page 6, equation (27): “" + IstarQuote + "” Every direction assignment in all four correlators is retained."),
            Node("values", "All orthonormal-frame absolute values", ValuesFormula(),
                "This set contains every absolute value from equation (27) over the three orthonormal pairs in equation (30). The existential direction parameters all have type Fin 3 → Real."),
            Node("EGHZ", "The GHZ measure", MeasureFormula(),
                "Section V.B, printed page 6, equation (30): “" + MeasureQuote + "” The definition is one half times the supremum of values(rho). For every product density in the conclusion this set is nonempty and bounded above."),
            Node("claim", "The exact A|BC constant", ClaimFormula(),
                "Section I, printed page 2, equation (1): “" + SpinQuote + "” Section V.B, printed page 6, equation (27): “" + IstarQuote + "” Section V.B, printed page 6, equation (30): “" + MeasureQuote + "” Section V.C, printed page 7, equation (37): “" + ClaimQuote + "” The A|BC class is rhoA kronecker rhoBC with arbitrary density factors. The encoding states the universal upper bound and existence of an attaining density product, which together give the displayed supremum. The B|AC and C|AB symmetry statement and convex-mixture conclusions are outside this claim."),
            Describe.Lean(DescribeId.Create("ghz-half-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The exact constant is one half"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a product density, the functional factors as u f11 − u uprime² f22 f12 f21. Variance of a real linear combination of anticommuting Hermitian involutions bounds the sum of their squared expectations by one. Applying this to the two overlapping pairs on the same BC state bounds |f12 f21| by 1−|f11|². Consequently the absolute functional is at most q [x+(1−q²)(1−x²)], where q=|u| and x=|f11|. If 1−q² is at most one half, the bracket is at most one. Otherwise q≤3/4 and the bracket≤5/4, giving at most 15/16. The product |0⟩⟨0| tensor |Φ⁺⟩⟨Φ⁺| attains one half using direction pairs (z,x),(x,z),(x,z). No convexity or bound for mixtures across partitions follows from this conclusion."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wu-zhong-wu-2026-ghz-measure-biseparable-half"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("ghz-half-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula N(string value) => new Formula.Symbol(FormulaIdentifier.Create(value));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(int n) => Call("Fin", new Formula.Number(n));
    private static Formula Dir() => Parenthesized(Seq(Fin(3), To, N("Real")));
    private static Formula ProdType(Formula a, Formula b) => Parenthesized(Seq(a, Times, b));
    private static Formula ThreeIndex() => ProdType(Fin(2), ProdType(Fin(2), Fin(2)));
    private static Formula Mat(Formula index) => Call("Matrix", index, index, N("Complex"));
    private static Formula ThreeMat() => Mat(ThreeIndex());
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula Instance(string name, Formula n) => Seq(OpenBracket, Call(name, n), CloseBracket, Sp);
    private static Formula SpinExpression(Formula n) => Call("blochMatrix", D(0),
        Call("toLp", D(2), Seq(LambdaLower, Sp, N("i"), Colon, Fin(3), Comma,
            Mul(D(2), new Formula.Apply(n, [N("i")])))));
    private static Formula OrthonormalExpression(Formula a, Formula b) =>
        Call("Orthonormal", N("Real"), Call("vecCons", Call("toLp", D(2), a),
            Call("vecCons", Call("toLp", D(2), b), N("vecEmpty"))));
    private static Formula DensityFormula()
    {
        var n = N("n"); var rho = N("rho");
        return All("n", N("Type"), Seq(Instance("Fintype", n), All("rho", Mat(n),
            IffTo(Call("IsDensity", rho), And(Call("PosSemidef", rho), Eqn(Call("trace", rho), D(1)))))));
    }
    private static Formula ExpectFormula()
    {
        var n = N("n"); var rho = N("rho"); var a = N("A");
        return All("n", N("Type"), Seq(Instance("Fintype", n), Instance("DecidableEq", n),
            All("rho", Mat(n), All("A", Mat(n), Eqn(Call("expect", rho, a), Call("re", Call("trace", Mul(a, rho))))))));
    }
    private static Formula ThreeDirections(Formula body) => All("a", Dir(), All("b", Dir(), All("c", Dir(), body)));
    private static Formula Frames(bool existential, Formula body)
    {
        foreach (var name in new[] { "c2", "c1", "b2", "b1", "a2", "a1" })
            body = existential ? Ex(name, Dir(), body) : All(name, Dir(), body);
        return body;
    }
    private static Formula ObservableFormula() => ThreeDirections(Eqn(Call("observable", N("a"), N("b"), N("c")),
        Call("kronecker", SpinExpression(N("a")), Call("kronecker", SpinExpression(N("b")), SpinExpression(N("c"))))));
    private static Formula CorrelationFormula() => All("rho", ThreeMat(), ThreeDirections(
        Eqn(Call("E", N("rho"), N("a"), N("b"), N("c")), Call("expect", N("rho"), Call("observable", N("a"), N("b"), N("c"))))));
    private static Formula IstarCall(Formula rho) => Call("Istar", rho, N("a1"), N("a2"), N("b1"), N("b2"), N("c1"), N("c2"));
    private static Formula IstarFormula()
    {
        var rho = N("rho");
        return All("rho", ThreeMat(), Frames(false, Eqn(IstarCall(rho), Sub(Call("E", rho, N("a1"), N("b1"), N("c1")),
            Mul(Mul(Call("E", rho, N("a1"), N("b2"), N("c2")), Call("E", rho, N("a2"), N("b1"), N("c2"))),
                Call("E", rho, N("a2"), N("b2"), N("c1")))))));
    }
    private static Formula ValuesFormula()
    {
        var rho = N("rho"); var v = N("v");
        var predicate = Frames(true, And(OrthonormalExpression(N("a1"), N("a2")),
            And(OrthonormalExpression(N("b1"), N("b2")), And(OrthonormalExpression(N("c1"), N("c2")), Eqn(v, Call("abs", IstarCall(rho)))))));
        return All("rho", ThreeMat(), Eqn(Call("values", rho), Seq(OpenBrace, v, Colon, N("Real"), Mid, predicate, CloseBrace)));
    }
    private static Formula MeasureFormula() => All("rho", ThreeMat(), Eqn(Call("EGHZ", N("rho")),
        Mul(Half(), Call("sSup", Call("values", N("rho"))))));
    private static Formula ProductMeasure() => Call("EGHZ", Call("kronecker", N("rhoA"), N("rhoBC")));
    private static Formula ClaimBody() => And(
        All("rhoA", N("QubitMatrix"), All("rhoBC", N("TwoQubitMatrix"),
            Imp(Call("IsDensity", N("rhoA")), Imp(Call("IsDensity", N("rhoBC")), Leq(ProductMeasure(), Half()))))),
        Ex("rhoA", N("QubitMatrix"), Ex("rhoBC", N("TwoQubitMatrix"),
            And(Call("IsDensity", N("rhoA")), And(Call("IsDensity", N("rhoBC")), Eqn(ProductMeasure(), Half()))))));
    private static Formula ClaimFormula() => IffTo(N("claim"), ClaimBody());
}
