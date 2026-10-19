using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class NonselectiveNegativityGainOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/zuppardo2019entanglementgain");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every pure two-qubit state, the largest negativity after a non-selective projective measurement is half its initial negativity plus one quarter.",
        H("The optimal negativity of a non-selective two-qubit measurement"),
        Blocks(
            Paragraph(Text(
                "Vectors have complex coordinates indexed by Fin(2) × Fin(2), and operators are complex matrices on this product index. The symbol Uᴴ denotes the conjugate transpose, star denotes coordinatewise complex conjugation, and normSq is the squared complex modulus. The trace norm is the sum of singular values. The negativity is "),
                Math(In(NegativityFormula())),
                Text(
                    ". Here Γ is partial transposition on the second factor: the entry with row (i, j) and column (k, l) becomes the original entry with row (i, l) and column (k, j).")),
            Paragraph(Text("The rank-one density ψψ†, also written ψψᴴ, is "),
                Ref("D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity"),
                Text(". Its entries are ψ(i) times the conjugate of ψ(j); for a unit vector it is the pure-state density matrix.")),
            Node("measured", "The non-selective measurement map", MeasuredFormula(),
                "Theorem 2 gives the post-measurement state as the sum of the basis projectors weighted by the squared overlaps with the input vector. Here the columns u_j of U give those basis vectors, and the coefficient is (UᴴρU)_jj. For unitary U and ρ = ψψ† this is |⟨u_j, ψ⟩|². The definition itself accepts arbitrary matrices U and ρ; smul denotes scalar multiplication.",
                DescribeRole.Definition),
            Node("claim", "The global two-qubit negativity optimum", ClaimFormula(),
                "For every unit two-qubit vector ψ, every unitary U satisfies N(measured(U, ψψ†)) ≤ N(ψψ†)/2 + 1/4, and some unitary U attains equality. Here N denotes the negativity defined above. Section I.E obtains this value within the family of measurement bases in Eq. (28), through Eq. (33), and asks whether it is optimal over all measurement bases. The two clauses state that global bound and its attainment.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonselective-negativity-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The sharp bound and an attaining measurement"),
                StatementSource.FromAuthor(Disp(X("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let ρ = ψψ† for a unit vector and let σ = measured(U, ρ) = Σ_j p_j P_j, where P_j are the orthogonal rank-one column projectors of a unitary U. Orthogonality gives Tr(σ²) = Σ_j p_j² = Tr(σρ). Since ρ² = ρ and Tr(ρ) = 1, it follows that Tr((2σ − ρ)²) = 1. Thus the Hermitian matrix X = 2σ − ρ has Frobenius norm one.")),
                    Paragraph(Text(
                        "Partial transposition permutes the matrix entries, so it preserves the Frobenius norm. In dimension four the Hilbert–Schmidt Hölder inequality gives ‖Y‖₁ ≤ 2‖Y‖_F, hence ‖X^Γ‖₁ ≤ 2. The triangle inequality applied to 2σ^Γ = ρ^Γ + X^Γ yields 2‖σ^Γ‖₁ ≤ ‖ρ^Γ‖₁ + 2. Substitution into the definition of negativity gives N(σ) ≤ N(ρ)/2 + 1/4.")),
                    Paragraph(Text(
                        "For attainment, the Schmidt decomposition gives local coordinates ψ₀ = a|00⟩ + b|11⟩ with a, b nonnegative and a² + b² = 1. A real orthogonal measurement basis in the span of |00⟩ and |11⟩, completed by |01⟩ and |10⟩, gives the half-pure, half-Bell state σ₀ = (ψ₀ψ₀† + ΦΦ†)/2, where Φ = (|00⟩ + |11⟩)/√2. Its partially transposed eigenvalues are a²/2 + 1/4, b²/2 + 1/4, ab/2 + 1/4, and −(ab/2 + 1/4). Consequently N(σ₀) = ab/2 + 1/4 = N(ψ₀ψ₀†)/2 + 1/4. Local unitaries transport this measurement back to ψ and preserve negativity. This attaining state is the construction of Theorem 3; together with the bound it establishes the global optimality asked in Section I.E."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zuppardo-ganardi-miller-bandyopadhyay-paterek-2018-nonselective-negativity-optimum"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("nonselective-negativity-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Index() => Parenthesized(Seq(Call("Fin", D(2)), Sp, Times, Sp, Call("Fin", D(2))));
    private static Formula VectorType() => Parenthesized(new Formula.TypeArrow(Index(), Complex()));
    private static Formula MatrixType() => Call("Matrix", Index(), Index(), Complex());
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula At(Formula value, params Formula[] arguments) => new Formula.Apply(value, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula LambdaOver(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(variable, type), Sp, Mapsto, Sp, body));
    private static Formula Adjoint(Formula value) => new Formula.Power(Parenthesized(value), X("H"));
    private static Formula Transposed(Formula value) => new Formula.Power(Parenthesized(value), Gamma);
    private static Formula TraceNorm(Formula value) => new Formula.Subscript(new Formula.Norm(value), D(1));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Unitary(Formula value) => Seq(value, Sp, InMacro, Sp, Call("unitaryGroup", Index(), Complex()));

    private static Formula NegativityFormula() => All(Rho, MatrixType(), Equal(Call("negativity", Rho),
        new Formula.Fraction(Subtract(TraceNorm(Transposed(Rho)), D(1)), D(2))));

    private static Formula MeasuredFormula()
    {
        var u = X("U");
        var j = X("j");
        var column = LambdaOver(X("i"), Index(), At(u, X("i"), j));
        var coefficient = At(Parenthesized(Mul(Parenthesized(Mul(Adjoint(u), Rho)), u)), j, j);
        return All(u, MatrixType(), All(Rho, MatrixType(), Equal(Call("measured", u, Rho),
            SumOver(j, Index(), Call("smul", coefficient, Call("vecMulVec", column, Call("star", column)))))));
    }

    private static Formula ClaimFormula()
    {
        var u = X("U");
        var rho = Mul(Psi, Adjoint(Psi));
        var value = Call("negativity", Call("measured", u, rho));
        var bound = Add(new Formula.Fraction(Call("negativity", rho), D(2)), new Formula.Fraction(D(1), D(4)));
        var normalized = Equal(SumOver(X("i"), Index(), Call("normSq", At(Psi, X("i")))), D(1));
        var body = All(Psi, VectorType(), Imp(normalized,
            And(All(u, MatrixType(), Imp(Unitary(u), Leq(value, bound))),
                Some(u, MatrixType(), And(Unitary(u), Equal(value, bound))))));
        return Iff(X("claim"), body);
    }
}
