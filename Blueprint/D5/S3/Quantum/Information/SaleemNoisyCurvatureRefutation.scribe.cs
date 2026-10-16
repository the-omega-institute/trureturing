using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SaleemNoisyCurvatureRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/saleem2025curvature");
    private const string Conjecture = "For the case with decay also there are more general examples we can consider but in all cases we conjecture that CoE ≤ QFI with equality at specific points.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit amplitude-damped probe starting at diag(1,11,3,1)/16 has smooth concurrence curvature 1 and quantum Fisher information 8/15 at t=1, kappa=log 2 and g=pi/4.",
        H("Noisy entanglement curvature can exceed quantum Fisher information"),
        Blocks(
            Node("jump1", "First amplitude-damping jump", Disp(Eq(X("jump1"),
                Call("kroneckerMap", MultiplyFunction(), X("sigmaMinus"), Typed(D(1), QubitMatrices)))),
                "Equation (41), p. 8, and Appendix B use the jump operators σ₋ on the two qubits, with σ₋ = (σx − iσy)/2. The computational basis is |ij⟩ indexed by (i,j) in Fin 2 × Fin 2. The reused sigmaMinus is the matrix [[0,0],[1,0]], so this is σ₋ ⊗ I.", true),
            Node("jump2", "Second amplitude-damping jump", Disp(Eq(X("jump2"),
                Call("kroneckerMap", MultiplyFunction(), Typed(D(1), QubitMatrices), X("sigmaMinus")))),
                "Equation (41), p. 8: the second jump is I ⊗ σ₋. Both identity matrices are complex two-by-two matrices.", true),
            Node("hamiltonian", "Flip-flop Hamiltonian", HamiltonianFormula(),
                "Equation (21), p. 4, specialized to etaXY=1: Hprobe = g(σ₋⁽¹⁾σ₊⁽²⁾ + σ₊⁽¹⁾σ₋⁽²⁾). Its only nonzero entries are g at (01,10) and (10,01). The complex cast of g is displayed explicitly.", true),
            Node("dissipator", "Lindblad dissipator", DissipatorFormula(),
                "Equation (41), p. 8, defines D[O](rho) = O rho O† − (O† O rho + rho O† O)/2. conjTranspose is the matrix adjoint; the factor 1/2 is a complex scalar acting by smul.", true),
            Node("generator", "Open evolution generator", GeneratorFormula(),
                "Equation (41), p. 8: the commutator term is −i[Hprobe,rho], and the two amplitude-damping dissipators each have rate kappa. The rate is cast to the complex numbers before scalar multiplication.", true),
            Node("IsTrajectory", "Solutions of the initial-value problem", TrajectoryFormula(),
                "Equation (41), p. 8, with initial state rhoZero independent of g. Every matrix entry has the stated time derivative, for every real g and t. HasDerivAt is the real-variable derivative with complex values.", true),
            Node("sigmaYY", "Spin-flip matrix", Disp(Eq(X("sigmaYY"),
                Call("kroneckerMap", MultiplyFunction(), PauliY(), PauliY()))),
                "Section II, p. 3, uses σy ⊗ σy in the spin-flip product. Here σy is the complex matrix [[0,−i],[i,0]].", true),
            Node("concurrence", "Wootters concurrence", ConcurrenceFormula(),
                "Section II, p. 3: 'the λi are the square roots of the eigenvalues, in decreasing order, of the matrix R = ρ(σy ⊗ σy)ρ∗(σy ⊗ σy).' The concurrence formula takes max(0,λ1−λ2−λ3−λ4). The characteristic-polynomial roots retain algebraic multiplicity; map applies sqrt to each real part, then sort orders the resulting real multiset decreasingly. List.getD uses zero-based indices and default zero. The star in Matrix.map conjugates each entry, without transposing.", true),
            Node("derivG", "Derivative with respect to the coupling", DerivFormula(),
                "Section II, equation (7), p. 3: 'we define the curvature of entanglement (CoE) as' CoE ≡ −∂g² C(rho). The matrix derivative here differentiates each entry in g at fixed t; Matrix.of constructs the matrix with those entries.", true),
            Node("IsSLD", "Symmetric logarithmic derivative", SldFormula(),
                "Section II, p. 2: the Hermitian SLD L satisfies dRho=(rho L+L rho)/2, and QFI=Tr(rho L²). The displayed predicate includes both Hermiticity and the SLD equation.", true),
            Node("claim", "The noisy curvature conjecture", Disp(Iff(X("claim"), ClaimBody())),
                "Section IV.B, p. 9: '" + Conjecture + "' Encoding: rhoZero is any density matrix, kappa and t are positive real numbers, and rho solves (41) with that initial state. At every g where the concurrence is twice continuously differentiable, the negative second derivative is at most the real part of Tr(rho L²), for every Hermitian SLD L. IsDensity is the reused predicate PosSemidef and trace one. Matrix indices are pairs, with the first coordinate the first qubit. The twice-continuously-differentiable condition restricts the comparison to smooth points.", true),
            Node("result", "Refutation at positive damping", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take rhoZero=diag(1,11,3,1)/16, kappa=log 2 and t=1. At g=pi/4 the evolved state is [[1,0,0,0],[0,15,8i,0],[0,−8i,15,0],[0,0,0,33]]/64. Its spin-flip spectrum is {529,49,33,33}/4096. Near that point its concurrence equals sin(2g)/4−sqrt(33)/32, hence its curvature is 1. The Hermitian matrix L=diag(0,−16/15,16/15,0) satisfies the SLD equation and gives QFI=8/15. The conjectured inequality would require 1≤8/15.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("saleem-et-al-2025-noisy-curvature-of-entanglement"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("scoe-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula X(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Indices => Parenthesized(Seq(Call("Fin", D(2)), Sp, Times, Sp, Call("Fin", D(2))));
    private static Formula Matrices => Call("Matrix", Indices, Indices, C);
    private static Formula QubitMatrices => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), C);
    private static Formula Family => Seq(R, Sp, To, Sp, R, Sp, To, Sp, Matrices);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Field(Formula receiver, string name) => Seq(Parenthesized(receiver), Dot, Operatorname, Grp(X(name)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, X(name), Colon, type, Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) => Seq(Operatorname, Grp(X("fun")), Sp, X(name), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Cast(Formula value) => Typed(Call("val", value), C);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Pair(byte a, byte b) => Parenthesized(Seq(D(a), Comma, D(b)));
    private static Formula Adjoint(Formula a) => App(Q("Matrix", "conjTranspose"), a);
    private static Formula Smul(Formula a, Formula b) => App(Q("SMul", "smul"), a, b);
    private static Formula Half => Typed(new Formula.Fraction(D(1), D(2)), C);
    private static Formula MultiplyFunction() => Fun("x", C, Fun("y", C, Mul(X("x"), X("y"))));
    private static Formula PauliY() => Typed(Seq(Bang, Bang, OpenBracket,
        D(0), Comma, Negate(X("I")), Semi, X("I"), Comma, D(0), CloseBracket), QubitMatrices);

    private static Formula HamiltonianFormula()
    {
        var condition = Or(And(Eq(X("a"), Pair(0, 1)), Eq(X("b"), Pair(1, 0))),
            And(Eq(X("a"), Pair(1, 0)), Eq(X("b"), Pair(0, 1))));
        return Disp(All("g", R, Eq(Call("hamiltonian", X("g")), Fun("a", Indices, Fun("b", Indices,
            Seq(Operatorname, Grp(X("if")), Sp, condition, Sp, Operatorname, Grp(X("then")), Sp,
                Cast(X("g")), Sp, Operatorname, Grp(X("else")), Sp, D(0)))))));
    }

    private static Formula DissipatorFormula() => Disp(All("O", Matrices, All("rho", Matrices,
        Eq(Call("dissipator", X("O"), X("rho")),
            Sub(Mul(Mul(X("O"), X("rho")), Adjoint(X("O"))), Smul(Half,
                Add(Mul(Mul(Adjoint(X("O")), X("O")), X("rho")),
                    Mul(X("rho"), Parenthesized(Mul(Adjoint(X("O")), X("O")))))))))));

    private static Formula GeneratorFormula() => Disp(All("g", R, All("kappa", R, All("rho", Matrices,
        Eq(Call("generator", X("g"), X("kappa"), X("rho")), Add(
            Smul(Negate(X("I")), Sub(Mul(Call("hamiltonian", X("g")), X("rho")),
                Mul(X("rho"), Call("hamiltonian", X("g"))))),
            Smul(Cast(X("kappa")), Add(Call("dissipator", X("jump1"), X("rho")),
                Call("dissipator", X("jump2"), X("rho"))))))))));

    private static Formula TrajectoryFormula() => Disp(All("rhoZero", Matrices, All("kappa", R,
        All("rho", Family, Iff(Call("IsTrajectory", X("rhoZero"), X("kappa"), X("rho")),
            And(All("g", R, Eq(App(X("rho"), X("g"), D(0)), X("rhoZero"))),
                All("g", R, All("t", R, All("a", Indices, All("b", Indices,
                    Call("HasDerivAt", Fun("s", R, App(X("rho"), X("g"), X("s"), X("a"), X("b"))),
                        App(Call("generator", X("g"), X("kappa"), App(X("rho"), X("g"), X("t"))), X("a"), X("b")), X("t"))))))))))));

    private static Formula ConcurrenceFormula()
    {
        var product = Mul(Mul(Mul(X("rho"), X("sigmaYY")),
            App(Field(X("rho"), "map"), X("star"))), X("sigmaYY"));
        var roots = Field(Field(product, "charpoly"), "roots");
        var squareRoots = App(Field(roots, "map"), Fun("z", C, App(Q("Real", "sqrt"), Field(X("z"), "re"))));
        var sorted = App(Field(squareRoots, "sort"), Fun("x", R, Fun("y", R, Le(X("y"), X("x")))));
        Formula Entry(byte n) => App(Field(X("l"), "getD"), D(n), D(0));
        return Disp(All("rho", Matrices, Eq(Call("concurrence", X("rho")),
            Seq(Operatorname, Grp(X("let")), Sp, X("l"), F.Eq, sorted, Semi, Sp,
                Call("max", D(0), Sub(Sub(Sub(Entry(0), Entry(1)), Entry(2)), Entry(3)))))));
    }

    private static Formula DerivFormula() => Disp(All("rho", Family, All("g", R, All("t", R,
        Eq(Call("derivG", X("rho"), X("g"), X("t")), App(Q("Matrix", "of"),
            Fun("a", Indices, Fun("b", Indices, Call("deriv", Fun("h", R,
                App(X("rho"), X("h"), X("t"), X("a"), X("b"))), X("g"))))))))));

    private static Formula SldFormula() => Disp(All("rho", Matrices, All("dRho", Matrices, All("L", Matrices,
        Iff(Call("IsSLD", X("rho"), X("dRho"), X("L")),
            And(App(Q("Matrix", "IsHermitian"), X("L")),
                Eq(X("dRho"), Smul(Half, Add(Mul(X("rho"), X("L")), Mul(X("L"), X("rho")))))))))));

    private static Formula ClaimBody()
    {
        var at = App(X("rho"), X("g"), X("t"));
        var scalar = Fun("h", R, Call("concurrence", App(X("rho"), X("h"), X("t"))));
        var secondDerivative = Call("deriv", Call("deriv", scalar), X("g"));
        var qfi = Field(Field(Mul(Mul(at, X("L")), X("L")), "trace"), "re");
        var conclusion = Imp(Call("IsSLD", at, Call("derivG", X("rho"), X("g"), X("t")), X("L")),
            Le(Negate(Parenthesized(secondDerivative)), qfi));
        var point = All("g", R, Imp(Call("ContDiffAt", R, D(2), scalar, X("g")),
            All("L", Matrices, conclusion)));
        var assumptions = Imp(Call("IsDensity", X("rhoZero")), Imp(Lt(D(0), X("kappa")),
            Imp(Lt(D(0), X("t")), Imp(Call("IsTrajectory", X("rhoZero"), X("kappa"), X("rho")), point))));
        return All("rhoZero", Matrices, All("kappa", R, All("t", R, All("rho", Family, assumptions))));
    }
}
