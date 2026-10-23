using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QubitWassersteinCouplingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/bunthpitriktitkosvirosztek2024wasserstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qubit coupling optimization and the exact Pauli self cost.",
        H("QubitWassersteinCouplings"),
        Blocks(
            Node("couplings", Disp(All("d", Nat(), All("rho", Mat(V("d")), All("omega", Mat(V("d")), Eqn(C("couplings", V("rho"), V("omega")), SetOf("pi", ProductMat(V("d")), AndF(AndF(PSD(V("pi")), Eqn(Trace(V("pi")), D(1))), AndF(Eqn(QC("PartialTraceMutualInformation", "partialTraceRight", V("pi")), V("omega")), Eqn(QC("PartialTraceMutualInformation", "partialTraceLeft", V("pi")), TransposeF(V("rho"))))))))))), "The source §1.2 coupling set consists of positive semidefinite trace-one matrices on the product index type, with second-factor trace omega and first-factor trace rho transpose. The partialTraceRight and partialTraceLeft are literally the explicit sums over the traced-out factor.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("cost", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("pi", ProductMat(V("d")), Eqn(C("cost", V("A"), V("pi")), SumF("j", FinF(V("k")), QC("RCLike", "re", Trace(Mul(Mul(Sub(Kron(Apply(V("A"), V("j")), D(1)), Kron(D(1), TransposeF(Apply(V("A"), V("j"))))), V("pi")), Sub(Kron(Apply(V("A"), V("j")), D(1)), Kron(D(1), TransposeF(Apply(V("A"), V("j"))))))))))))))), "The trace cost is equation (eq:2-Wass-quant-def), with transpose on the dual factor and its real part made explicit.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("D2", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("rho", Mat(V("d")), All("omega", Mat(V("d")), Eqn(C("D2", V("A"), V("rho"), V("omega")), C("sInf", QC("Set", "image", C("cost", V("A")), C("couplings", V("rho"), V("omega"))))))))))), "The quadratic quantum Wasserstein distance is the infimum in equation (eq:2-Wass-quant-def).", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("dA", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("rho", Mat(V("d")), All("omega", Mat(V("d")), Eqn(C("dA", V("A"), V("rho"), V("omega")), Root(Sub(C("D2", V("A"), V("rho"), V("omega")), Div(Add(C("D2", V("A"), V("rho"), V("rho")), C("D2", V("A"), V("omega"), V("omega"))), D(2))))))))))), "The divergence is equation (eq:mod-qw-dist-def); the displayed fraction is real division.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("CW", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("Phi", Maps(V("d")), Eqn(C("CW", V("A"), V("Phi")), C("sSup", SetOf("x", Real(), Ex("rho", Mat(V("d")), AndF(State(V("rho")), Eqn(V("x"), C("dA", V("A"), V("rho"), Apply(V("Phi"), V("rho")))))))))))))), "Source §5.1, PDF p. 17, verbatim: “Given a finite collections of observables 𝒜={A₁, …, Aₖ}, let us define the Wasserstein complexity of a channel Φ:𝒮(ℋ)→𝒮(ℋ) by C_W(Φ):=max_{ρ∈𝒮(ℋ)} d_𝒜(ρ, Φ(ρ)).” The finite-dimensional source maximum is encoded by the supremum of its values; CW_bddAbove supplies boundedness.", AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("product_coupling", Disp(All("d", Nat(), All("rho", Mat(V("d")), All("omega", Mat(V("d")), Imp(State(V("rho")), Imp(State(V("omega")), Mem(Kron(V("omega"), TransposeF(V("rho"))), C("couplings", V("rho"), V("omega"))))))))), "The product of the output state and the transposed input state is an admissible coupling.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("couplings_nonempty", Disp(All("d", Nat(), All("rho", Mat(V("d")), All("omega", Mat(V("d")), Imp(State(V("rho")), Imp(State(V("omega")), QC("Set", "Nonempty", C("couplings", V("rho"), V("omega"))))))))), "Every pair of density states has a coupling.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("D2_le_cost", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("rho", Mat(V("d")), All("omega", Mat(V("d")), All("pi", ProductMat(V("d")), Imp(All("j", FinF(V("k")), QC("Matrix", "IsHermitian", Apply(V("A"), V("j")))), Imp(Mem(V("pi"), C("couplings", V("rho"), V("omega"))), LeqF(C("D2", V("A"), V("rho"), V("omega")), C("cost", V("A"), V("pi")))))))))))), "Every admissible coupling bounds the infimum from above.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("pauli_hermitian", Disp(All("j", FinF(D(3)), QC("Matrix", "IsHermitian", Apply(QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), V("j"))))), "Every observable in the Pauli triple is Hermitian.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("ptrace2_left", Disp(Ptrace2LeftFormula()), "Conjugating a two-qubit operator by a local matrix on the first factor conjugates its second-factor partial trace by that matrix.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("overlap", Disp(All("P", ProductMat(D(2)), Eqn(C("overlap", V("P")), ReF(C("dotProduct", C("star", IdentityVector()), QC("Matrix", "mulVec", V("P"), IdentityVector())))))), "The unnormalized Bell overlap is the quadratic form of P on Function.uncurry of the identity matrix.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("pauli_cost", Disp(All("P", ProductMat(D(2)), Eqn(C("cost", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), V("P")), Sub(Mul(D(8), ReF(Trace(V("P")))), Mul(D(4), C("overlap", V("P"))))))), "The Pauli cost operator is 8 times the identity minus 4 times the unnormalized Bell rank-one operator, equivalently 8 times the difference of the identity and the normalized Bell projector.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("CW_bddAbove", Disp(All("d", Nat(), All("k", Nat(), All("A", Arrow(FinF(V("k")), Mat(V("d"))), All("Phi", Maps(V("d")), Imp(All("j", FinF(V("k")), QC("Matrix", "IsHermitian", Apply(V("A"), V("j")))), C("BddAbove", SetOf("x", Real(), Ex("rho", Mat(V("d")), AndF(State(V("rho")), Eqn(V("x"), C("dA", V("A"), V("rho"), Apply(V("Phi"), V("rho")))))))))))))), "The complexity value set is bounded above, including the empty zero-dimensional domain.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("pureCoupling", Disp(All("d", Nat(), All("S", Mat(V("d")), Eqn(C("pureCoupling", V("S")), QC("PureStateHandshake", "rankOneDensity", QC("Function", "uncurry", V("S"))))))), "The square-root coupling reuses the frozen rank-one density construction on the vectorized matrix.", AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("pureCoupling_psd", Disp(All("d", Nat(), All("S", Mat(V("d")), PSD(C("pureCoupling", V("S")))))), "A vectorized outer product is positive semidefinite.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("ptrace2_pure", Disp(All("d", Nat(), All("S", Mat(V("d")), Eqn(QC("PartialTraceMutualInformation", "partialTraceRight", C("pureCoupling", V("S"))), Mul(V("S"), Adj(V("S"))))))), "The second-factor trace of the vectorized coupling is S times S conjugate transpose.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("ptrace1_pure", Disp(All("d", Nat(), All("S", Mat(V("d")), Eqn(QC("PartialTraceMutualInformation", "partialTraceLeft", C("pureCoupling", V("S"))), TransposeF(Mul(Adj(V("S")), V("S"))))))), "The first-factor trace is the transpose of S conjugate transpose times S.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("overlap_pure", Disp(All("S", Mat(D(2)), Eqn(C("overlap", C("pureCoupling", V("S"))), QC("Complex", "normSq", Trace(V("S")))))), "The Bell overlap of the vectorized coupling is the squared complex norm of its trace.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("diagState_isState", Disp(All("a", Real(), All("b", Real(), Imp(LeqF(D(0), V("a")), Imp(LeqF(D(0), V("b")), Imp(Eqn(Add(V("a"), V("b")), D(1)), State(Diagonal(V("a"), V("b"))))))))), "Nonnegative diagonal entries summing to one give a density state.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("diag_self_cost", Disp(All("a", Real(), All("b", Real(), Imp(LeqF(D(0), V("a")), Imp(LeqF(D(0), V("b")), Imp(Eqn(Add(V("a"), V("b")), D(1)), Eqn(C("D2", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), Diagonal(V("a"), V("b")), Diagonal(V("a"), V("b"))), Sub(D(8), Mul(D(4), Sq(Add(Root(V("a")), Root(V("b"))))))))))))), "The diagonal optimum is attained by the vectorized square root; the principal-minor bound gives the matching lower bound.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("rotate_isState", Disp(All("U", Mat(D(2)), All("rho", Mat(D(2)), Imp(Eqn(Mul(Adj(V("U")), V("U")), D(1)), Imp(State(V("rho")), State(Evolution(V("U"), V("rho")))))))), "Unitary conjugation preserves density states.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("D2_rotate", Disp(All("U", Mat(D(2)), All("rho", Mat(D(2)), All("omega", Mat(D(2)), Imp(Eqn(Mul(Adj(V("U")), V("U")), D(1)), Imp(Eqn(Mul(V("U"), Adj(V("U"))), D(1)), Imp(State(V("rho")), Imp(State(V("omega")), Eqn(C("D2", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), Evolution(V("U"), V("rho")), Evolution(V("U"), V("omega"))), C("D2", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), V("rho"), V("omega"))))))))))), "The Pauli infimum is invariant under simultaneous unitary conjugation, by transporting couplings through U tensor conjugate U.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("self_cost_spectral", Disp(All("rho", Mat(D(2)), Imp(State(V("rho")), Ex("a", Real(), Ex("b", Real(), AndF(LeqF(D(0), V("a")), AndF(LeqF(D(0), V("b")), AndF(Eqn(Add(V("a"), V("b")), D(1)), AndF(Eqn(C("D2", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), V("rho"), V("rho")), Sub(D(8), Mul(D(4), Sq(Add(Root(V("a")), Root(V("b"))))))), Eqn(ReF(Trace(QC("CFC", "sqrt", V("rho")))), Add(Root(V("a")), Root(V("b"))))))))))))), "Spectral reduction supplies nonnegative eigenvalues summing to one, the exact self cost and the real trace of the positive square root.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("self_cost", Disp(All("rho", Mat(D(2)), Imp(State(V("rho")), Eqn(C("D2", QC("SteeringEllipsoidFullyEntangledFraction", "pauli"), V("rho"), V("rho")), Sub(D(8), Mul(D(4), Sq(ReF(Trace(QC("CFC", "sqrt", V("rho"))))))))))), "Section 4.1, Proposition 3, equation (35), states D²(ρ,ρ)=4(1−√(1−|bρ|²)); for eigenvalues (1±r)/2 this is 8−4(tr√ρ)², the displayed correspondence.", AssessedProvenance.FromLiterature(Source), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
        DescribeId.Create("qwc-" + name.Replace("_", "").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Ptrace2LeftFormula()
    {
        Formula u = V("U"), p = V("P");
        Formula local = Kron(u, D(1));
        Formula conjugated = Mul(Mul(local, p), Adj(local));
        return All("U", Mat(D(2)), All("P", ProductMat(D(2)),
            Eqn(QC("PartialTraceMutualInformation", "partialTraceRight", conjugated),
                Mul(Mul(u, QC("PartialTraceMutualInformation", "partialTraceRight", p)), Adj(u)))));
    }

    private static Formula IdentityVector() => QC("Function", "uncurry", Parenthesized(Seq(D(1), Sp, Colon, Sp, Mat(D(2)))));
    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(FormulaDsl.Id(owner)), Dot, Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(FormulaDsl.Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(FormulaDsl.Id(name))), [.. args]);
    private static Formula QC(string owner, string name, params Formula[] args) => args.Length == 0 ? Q(owner, name) : new Formula.Apply(Q(owner, name), [.. args]);
    private static Formula Apply(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqF(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula AndF(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Sq(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Nat() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula ComplexF() => Seq(Mathbb, Grp(FormulaDsl.Id("C")));
    private static Formula FinF(Formula size) => C("Fin", size);
    private static Formula PairType(Formula size) => C("Prod", FinF(size), FinF(size));
    private static Formula Mat(Formula size) => C("Matrix", FinF(size), FinF(size), ComplexF());
    private static Formula ProductMat(Formula size) => C("Matrix", PairType(size), PairType(size), ComplexF());
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Maps(Formula size) => C("LinearMap", ComplexF(), Mat(size), Mat(size));
    private static Formula Adj(Formula value) => QC("Matrix", "conjTranspose", value);
    private static Formula TransposeF(Formula value) => QC("Matrix", "transpose", value);
    private static Formula Trace(Formula value) => QC("Matrix", "trace", value);
    private static Formula ReF(Formula value) => QC("Complex", "re", value);
    private static Formula Root(Formula value) => QC("Real", "sqrt", value);
    private static Formula PSD(Formula value) => QC("Matrix", "PosSemidef", value);
    private static Formula State(Formula value) => QC("CoPRelativeQuantumnessRefutation", "IsDensity", value);
    private static Formula Kron(Formula left, Formula right) => QC("Matrix", "kronecker", left, right);
    private static Formula Diagonal(Formula a, Formula b) => QC("ProjectedUnistochasticDynamics", "diagonalState", Vector(a, b));
    private static Formula Evolution(Formula u, Formula rho) => QC("ProjectedUnistochasticDynamics", "unitaryEvolution", u, rho);
    private static Formula Vector(params Formula[] items) => Seq(Bang, OpenBracket, VectorItems(items), CloseBracket);
    private static Formula VectorItems(Formula[] items) => items.Length == 2 ? Seq(items[0], Comma, Sp, items[1]) : Seq(items[0], Comma, Sp, items[1], Comma, Sp, items[2]);
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, FormulaDsl.Id(name), Sp, Colon, Sp, type, Sp, Bar, Sp, body, CloseBrace);
    private static Formula SumF(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(FormulaDsl.Id(name), Sp, Colon, Sp, type), Sp, Parenthesized(body));
}
