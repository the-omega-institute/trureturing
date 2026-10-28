using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class GeometricDiscordMutualCorrelationBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/gwozdz2014discordspontaneous");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every two-qubit density matrix, maximal mutual correlation is at least the square root of normalized geometric discord measured on the first qubit.",
        H("Geometric discord and maximal mutual correlation"), Blocks(
            Paragraph(Text(
                "The two qubits are ordered A, B, with matrix indices in Fin(2) × Fin(2). "
                    + "Fin(2) indexes 0, 1 and Fin(3) indexes the three Pauli matrices. "
                    + "The symbol 1 denotes the identity matrix of the indicated size, "
                    + "kronecker(a,b) denotes a ⊗ b, and a star denotes conjugate transpose. "
                    + "Matrix norms are operator norms for the Euclidean norm on vectors; "
                    + "the norm of a complex scalar is its modulus. Re denotes real part. "
                    + "The symbols inf and sup denote the infimum and supremum of sets of real numbers.")),
            Node("measuredState", "Measurement on the first qubit", MeasuredStateFormula(),
                "For unitary U, let P_k = U single(k,k,1) U*, where single(k,k,1) has "
                    + "one in entry (k,k) and zero elsewhere. Thus P_k is the projector onto "
                    + "column k of U, and the displayed sum is Σ_k (P_k ⊗ I) ρ (P_k ⊗ I). "
                    + "It is the nonselective rank-one projective measurement on A. "
                    + "The matrix expression itself is defined for every U and every ρ."),
            Node("geometricDiscord", "Normalized geometric discord", GeometricDiscordFormula(),
                "The infimum ranges over all unitary 2 by 2 matrices U, hence all "
                    + "orthonormal measurement bases on A. The factor two is the source's "
                    + "normalization d/(d − 1) for d = 2. For a density matrix this is "
                    + "the normalized one-sided geometric discord D_G; the definition "
                    + "also applies to arbitrary complex two-qubit matrices."),
            Paragraph(Text("The Hilbert–Schmidt square in this definition is "),
                Ref("D5/S3/Quantum/Tomography/RankOneContextCommutator.hilbertSchmidtSquare"),
                Text(", given by Re tr(m* m) for every finite complex square matrix m. "
                    + "Cyclicity of trace gives Re tr(m* m) = Re tr(m m*).")),
            Node("localCovariance", "Covariance between the local algebras", LocalCovarianceFormula(),
                "The local matrices a and b act as a ⊗ I and I ⊗ b. Their covariance "
                    + "is the expectation of a ⊗ b minus the product of their separate "
                    + "expectations. The displayed expression is complex valued and "
                    + "requires no positivity or normalization assumption on ρ."),
            Node("maximalMutualCorrelation", "Maximal mutual correlation", MaximalMutualCorrelationFormula(),
                "Take the supremum of the moduli of local covariances over all complex "
                    + "2 by 2 matrices a and b of operator norm one. These matrices need "
                    + "not be Hermitian. For density matrices this is the source's "
                    + "maximal mutual correlation C_M between the two local algebras."),
            Node("connectedCorrelation", "Connected Pauli correlations", ConnectedCorrelationFormula(),
                "Write x_i = blochA(ρ,i), y_j = blochB(ρ,j), and T_ij = corr(ρ,i,j). "
                    + "These are the real parts of tr(ρ(σ_i ⊗ I)), tr(ρ(I ⊗ σ_j)), "
                    + "and tr(ρ(σ_i ⊗ σ_j)), respectively. The connected correlation "
                    + "matrix has entries Q_ij = T_ij − x_i y_j, as in the source's "
                    + "Pauli description of covariance."),
            Node("claim", "The two-qubit correlation bound", ClaimFormula(),
                "The proposition is the first inequality in Eq. (II.23): "
                    + "√D_G(ρ) ≤ C_M(ρ) for every positive semidefinite two-qubit matrix "
                    + "of trace one. It includes pure and mixed states. The source "
                    + "establishes the Bell-diagonal case and proposes the general "
                    + "mixed-state inequality on numerical evidence."),
            Node("rotateState", "Local change of basis", RotateStateFormula(),
                "Conjugation by U* on the first qubit expresses the state in the basis U."),
            PublishedTheorem("rotated_spin_witness", "Rotated spin correlations", RotatedSpinFormula(),
                "Unit spin observables in any local basis provide admissible covariance values, "
                    + "so the absolute connected correlation is bounded by maximal mutual correlation."),
            PublishedTheorem("marginal_basis", "A basis for the first marginal", MarginalBasisFormula(),
                "The spectral basis of the first marginal makes its first two Bloch coordinates zero. "
                    + "The construction includes a marginal proportional to the identity."),
            Describe.Lean(
                DescribeId.Create("geometric-discord-mutual-correlation-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Maximal mutual correlation bounds geometric discord"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let ρ be positive semidefinite with trace one. Its real Bloch "
                            + "vectors x and y and correlation tensor T give the expansion "
                            + "ρ = (I ⊗ I + Σ_i x_i σ_i ⊗ I + Σ_j y_j I ⊗ σ_j "
                            + "+ Σ_ij T_ij σ_i ⊗ σ_j)/4. Put Q = T − x yᵀ.")),
                    Paragraph(Text(
                        "Choose a unit vector u parallel to x when x ≠ 0, and any unit "
                            + "vector u when x = 0. Measure A in the eigenbasis of u·σ "
                            + "and set P = I − u uᵀ. Since Px = 0, the disturbance is "
                            + "δ = Σ_ij (PT)_ij σ_i ⊗ σ_j/4 and PT = PQ. Orthogonality "
                            + "of the Pauli tensors gives ‖δ‖₂² = ‖PQ‖_F²/4. For an "
                            + "orthonormal completion u, v, w, the discord therefore obeys "
                            + "D_G(ρ) ≤ ‖PQ‖_F²/2 = (‖Qᵀv‖² + ‖Qᵀw‖²)/2.")),
                    Paragraph(Text(
                        "For unit real vectors c and d, the spin observables c·σ and "
                            + "d·σ have operator norm one and covariance cᵀQd. If "
                            + "Qᵀv ≠ 0, choose c = v and d = Qᵀv/‖Qᵀv‖ to obtain "
                            + "C_M(ρ) ≥ ‖Qᵀv‖. If Qᵀv = 0, the same inequality "
                            + "follows from nonnegativity. Applying this also to w gives "
                            + "D_G(ρ) ≤ C_M(ρ)².")),
                    Paragraph(Text(
                        "Both quantities are nonnegative. The density-matrix estimate "
                            + "|tr(ρX)| ≤ ‖X‖ and compactness of the local unit spheres "
                            + "bound the covariance values, so their supremum is finite. "
                            + "Taking square roots proves √D_G(ρ) ≤ C_M(ρ)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gwozdz-jakobczyk-2013-geometric-discord-mutual-correlation-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("geometric-discord-mutual-correlation-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock PublishedTheorem(string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("geometric-discord-mutual-correlation-" + declaration.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula RotateStateFormula()
    {
        Formula u = F.Id("U"), v = Tensor(u, Identity());
        return All(u, Qubit(), All(Rho, TwoQubit(), Equal(Call("rotateState", u, Rho),
            Mul(Mul(Adjoint(v), Rho), v))));
    }

    private static Formula RotatedSpinFormula()
    {
        Formula u = F.Id("U"), c = F.Id("c"), d = F.Id("d");
        Formula vector = Seq(Index(3), To, Sp, Reals());
        Formula rotated = Call("rotateState", u, Rho);
        Formula value = Call("dotProduct", c, Call("mulVec", Call("connectedCorrelation", rotated), d));
        Formula absolute = Seq(Lvert, Sp, value, Rvert);
        return All(Rho, TwoQubit(), ImpliesTo(Call("PosSemidef", Rho),
            ImpliesTo(Equal(Call("trace", Rho), D(1)),
                All(u, Call("unitaryGroup", Index(2), Complexes()),
                    All(c, vector, All(d, vector,
                        ImpliesTo(Equal(Call("vlen", c), D(1)),
                            ImpliesTo(Equal(Call("vlen", d), D(1)),
                                LE(absolute, Call("maximalMutualCorrelation", Rho))))))))));
    }

    private static Formula MarginalBasisFormula()
    {
        Formula u = F.Id("U"), rotated = Call("rotateState", u, Rho);
        return All(Rho, TwoQubit(), ImpliesTo(Call("PosSemidef", Rho),
            Some(u, Call("unitaryGroup", Index(2), Complexes()),
                And(Equal(Call("blochA", rotated, D(0)), D(0)),
                    Equal(Call("blochA", rotated, D(1)), D(0))))));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Adjoint(Formula matrix) => Seq(matrix, Caret, Grp(Star));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Index(byte dimension) => Call("Fin", D(dimension));
    private static Formula Qubit() => Call("Matrix", Index(2), Index(2), Complexes());
    private static Formula TwoQubit()
    {
        Formula indices = Parenthesized(Seq(Index(2), Times, Sp, Index(2)));
        return Call("Matrix", indices, indices, Complexes());
    }
    private static Formula Identity() => Typed(D(1), Qubit());
    private static Formula Tensor(Formula left, Formula right) => Call("kronecker", left, right);

    private static Formula MeasuredStateFormula()
    {
        Formula u = F.Id("U"), k = F.Id("k");
        Formula projector = Parenthesized(Mul(Mul(u, Call("single", k, k, D(1))), Adjoint(u)));
        Formula local = Parenthesized(Tensor(projector, Identity()));
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(k, Index(2))), Sp,
            Parenthesized(Mul(Mul(local, Rho), local)));
        return All(u, Qubit(), All(Rho, TwoQubit(), Equal(Call("measuredState", u, Rho), sum)));
    }

    private static Formula GeometricDiscordFormula()
    {
        Formula u = F.Id("U");
        Formula disturbance = Parenthesized(Subtract(Rho, Call("measuredState", u, Rho)));
        Formula values = new Formula.SetBuilder(
            Call("Re", Call("tr", Mul(Adjoint(disturbance), disturbance))),
            u, Call("unitaryGroup", Index(2), Complexes()));
        return All(Rho, TwoQubit(), Equal(Call("geometricDiscord", Rho), Mul(D(2), Call("inf", values))));
    }

    private static Formula LocalCovarianceFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula joint = Call("tr", Mul(Rho, Parenthesized(Tensor(a, b))));
        Formula first = Call("tr", Mul(Rho, Parenthesized(Tensor(a, Identity()))));
        Formula second = Call("tr", Mul(Rho, Parenthesized(Tensor(Identity(), b))));
        return All(Rho, TwoQubit(), All(a, Qubit(), All(b, Qubit(),
            Equal(Call("localCovariance", Rho, a, b), Subtract(joint, Mul(first, second))))));
    }

    private static Formula MaximalMutualCorrelationFormula()
    {
        Formula r = F.Id("r"), a = F.Id("a"), b = F.Id("b");
        Formula values = Seq(OpenBrace, Sp, Typed(r, Reals()), Sp, Mid, Sp,
            Some(a, Qubit(), Some(b, Qubit(),
                And(Equal(new Formula.Norm(a), D(1)),
                    And(Equal(new Formula.Norm(b), D(1)),
                        Equal(r, new Formula.Norm(Call("localCovariance", Rho, a, b))))))),
            Sp, CloseBrace);
        return All(Rho, TwoQubit(), Equal(Call("maximalMutualCorrelation", Rho), Call("sup", values)));
    }

    private static Formula ConnectedCorrelationFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return All(Rho, TwoQubit(), All(i, Index(3), All(j, Index(3),
            Equal(Call("connectedCorrelation", Rho, i, j), Subtract(Call("corr", Rho, i, j),
                Mul(Call("blochA", Rho, i), Call("blochB", Rho, j)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula bound = LE(Seq(Sqrt, Grp(Call("geometricDiscord", Rho))),
            Call("maximalMutualCorrelation", Rho));
        Formula statement = All(Rho, TwoQubit(), ImpliesTo(Call("PosSemidef", Rho),
            ImpliesTo(Equal(Call("tr", Rho), D(1)), bound)));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(statement));
    }
}
