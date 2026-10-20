using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BadhaniDasNoisyUnitaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/badhani2026conditionalchannel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "White-noise mixtures of arbitrary bipartite unitaries with qubit conditioning attain the Choi-state upper bound on conditional min-entropy.",
        H("Conditional min-entropy of noisy unitaries"), Blocks(
            Node("dmax", "Max-relative entropy", "Dmax", DmaxFormula(),
                "Section II.2, page 10: “D_max(ρ‖σ) = log inf{λ ≥ 0 : ρ ≤ λσ}”, “where D_max(ρ‖σ) = +∞ if supp(ρ) ⊄ supp(σ).” The carrier n is finite. MatrixOrder is the Loewner order; real scalar multiplication and base-two logarithms are used. The value is in EReal, and the empty feasible set gives top.",
                AssessedProvenance.FromLiterature(Source)),
            Node("state-entropy", "Conditional min-entropy of a state", "condMinEntropy", StateEntropyFormula(),
                "Table I, page 11: “S_∞(A|B)_ρ := −inf_{σ∈St(B)} D_∞(ρ_{AB}‖1_A ⊗ σ_B).” DensityState Y is St(B); CStarMatrix.ofMatrix.symm converts its value to matrix coordinates. The two finite factors are X and Y.",
                AssessedProvenance.FromLiterature(Source)),
            Node("choi-operator", "The bipartite Choi operator", "choiN", ChoiFormula(),
                "Section V, page 18: “The Choi operator Γ^N of a bipartite channel N_{A′B′→AB} is Γ^N_{R_AAR_BB} = N(Γ_{R_AA′} ⊗ Γ_{R_BB′}), where Γ_{R_AA′} denotes a maximally entangled operator.” The matrix units implement this expression. The factors are ordered (R_A, A), (R_B, B), with A′ = A = Fin d and B′ = B = Fin 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("choi-state", "The normalized Choi state", "choiState", ChoiStateFormula(),
                "Section II, page 8: “The Choi state of a bipartite quantum channel N_{A′B′→AB} is Φ^N_{R_AAR_BB} = N(Φ_{R_AA′} ⊗ Φ_{R_BB′}).” The normalization is the inverse of the input dimension 2d. The expression is defined for every matrix map, and is a normalized state on the noisy-unitary maps in the theorem.",
                AssessedProvenance.FromLiterature(Source)),
            Node("channel-entropy", "Conditional min-entropy of a channel", "channelCondMinEntropy", ChannelEntropyFormula(),
                "Section V, page 18 gives “S_∞[A|B]_N := −inf_{Q∈Ch(B′,B)} D_∞[N_{A′B′→AB}‖R^1_{A′→A} ⊗ Q_{B′→B}]” and its equal Choi-operator expression “−inf_{Q∈Ch(B′,B)} D_∞(Γ^N_{R_AAR_BB}‖1_{R_AA} ⊗ Γ^Q_{R_BB})”. This definition uses that second expression, with QuantumChannel (Fin 2) (Fin 2) and the full matrix-unit expression for Γ^Q.",
                AssessedProvenance.FromLiterature(Source)),
            Node("noise", "A unitary mixed with white noise", "noisyUnitary", NoiseFormula(),
                "Section VI.1, page 31: “let N_p := pR^π + (1 − p)U for p ∈ [0, 1]”. Here R^π(Z) = tr(Z)1/(2d) and U(Z) = U Z U†. The definition allows every real p; the theorem restricts p to the stated interval.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Badhani–Das conjecture with qubit conditioning", "claim",
                Equal(Local("claim"), Parenthesized(ClaimBody())),
                "Section VI.1, page 31: “We conjecture that Proposition 10 can be extended to all unitaries with added white noise. We leave this as an open problem.” Proposition 10 says: “For an arbitrary unitary channel U_{A′B′→AB} such that |B′| = |B| = 2, we have S_∞[A|B]_U = S_∞(R_AA|R_BB)_{Φ^U} − log|A′|.” The dimension d ranges over all positive naturals, the unitary acts on Fin d × Fin 2, and p ranges over [0, 1]. No choice of unitary or bound on d is imposed.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("noisy-unitary-result"), DeclarationHandle.Create(Prefix + "result"),
                H("White noise preserves equality with the Choi-state bound"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The reduced two-qubit Choi matrix has both marginals maximally mixed. In the magic basis it is real symmetric, so its real orthonormal eigenvectors give a maximally entangled eigenbasis. Signs in this eigenbasis have unitary partners on the other factor. Their tensor products fix the pure Choi vector and the white-noise matrix. Averaging a feasible optimizer over these signs preserves its trace and makes it the normalized Choi matrix of a channel. The state and channel optimizations therefore have equal costs after scaling by d, which subtracts log₂ d from the entropy. The proof includes singular eigenvalues, the endpoints p = 0 and p = 1, and d = 1. Conditioning dimensions greater than two are outside this statement."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("noisy-unitary-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Local(string name) => Q(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesTo(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula FunctionTo(Formula left, Formula right) => Parenthesized(new Formula.TypeArrow(left, right));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => At(Q("Fin"), n);
    private static Formula Matrix(Formula n) => At(Q("Matrix"), n, n, Complex());
    private static Formula Input() => Product(Fin(X("d")), Fin(D(2)));
    private static Formula LeftFactor() => Product(Fin(X("d")), Fin(X("d")));
    private static Formula RightFactor() => Product(Fin(D(2)), Fin(D(2)));
    private static Formula ChoiIndex() => Product(LeftFactor(), RightFactor());
    private static Formula MapType() => FunctionTo(Matrix(Input()), Matrix(Input()));
    private static Formula S(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Mul(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Star, Sp, Parenthesized(right));
    private static Formula Tensor(Formula left, Formula right) => At(Q("Matrix", "kroneckerMap"),
        Seq(Q("fun"), Sp, X("a"), Sp, X("b"), Sp, Mapsto, Sp, X("a"), Star, X("b")), left, right);
    private static Formula CastReal(Formula value) => Typed(value, Real());
    private static Formula CastEReal(Formula value) => Typed(value, Q("EReal"));
    private static Formula One(Formula n) => Typed(D(1), Matrix(n));
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(
        Q("fun"), Sp, Typed(X(name), type), Sp, Mapsto, Sp, body);
    private static Formula Inf(string name, Formula type, Formula body) => At(Q("iInf"), Lambda(name, type, body));
    private static Formula Instances(string name, Formula body) => Seq(
        OpenBracket, At(Q("Fintype"), X(name)), CloseBracket, Sp,
        OpenBracket, At(Q("DecidableEq"), X(name)), CloseBracket, Sp, body);
    private static Formula Feasible() => And(LeqTo(D(0), X("t")), LeqTo(X("rho"), S(X("t"), X("sigma"))));

    private static Formula DmaxFormula()
    {
        Formula set = Seq(OpenBrace, Typed(X("t"), Real()), Sp, Mid, Sp, Feasible(), CloseBrace);
        Formula logarithm = CastEReal(At(Q("Real", "logb"), D(2), At(Q("sInf"), set)));
        Formula rhs = At(Q("ite"), Parenthesized(Some("t", Real(), Feasible())), logarithm, Q("Top", "top"));
        return All("n", Q("Type"), Instances("n", All("rho", Matrix(X("n")), All("sigma", Matrix(X("n")),
            Equal(At(Local("Dmax"), X("rho"), X("sigma")), rhs)))));
    }
    private static Formula StateEntropyFormula()
    {
        Formula sigma = At(Q("CStarMatrix", "ofMatrix", "symm"), Call("val", X("sigma")));
        Formula divergence = At(Local("Dmax"), X("rho"), Tensor(One(X("X")), sigma));
        Formula body = Equal(At(Local("condMinEntropy"), X("rho")),
            new Formula.Negate(Inf("sigma", At(Q("DensityState"), X("Y")), divergence)));
        return All("X", Q("Type"), Instances("X", All("Y", Q("Type"), Instances("Y",
            All("rho", Matrix(Product(X("X"), X("Y"))), body)))));
    }
    private static Formula Projection(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula ChoiFormula()
    {
        Formula x = X("x"), y = X("y");
        Formula row = Pair(Projection(Projection(x, 1), 1), Projection(Projection(x, 2), 1));
        Formula col = Pair(Projection(Projection(y, 1), 1), Projection(Projection(y, 2), 1));
        Formula outputRow = Pair(Projection(Projection(x, 1), 2), Projection(Projection(x, 2), 2));
        Formula outputCol = Pair(Projection(Projection(y, 1), 2), Projection(Projection(y, 2), 2));
        Formula body = At(X("N"), At(Q("Matrix", "single"), row, col, Typed(D(1), Complex())), outputRow, outputCol);
        return All("d", Nat(), All("N", MapType(), Equal(At(Local("choiN"), X("N")),
            Lambda("x", ChoiIndex(), Lambda("y", ChoiIndex(), body)))));
    }
    private static Formula ChoiStateFormula() => All("d", Nat(), All("N", MapType(),
        Equal(At(Local("choiState"), X("N")), S(new Formula.Power(CastReal(Typed(Mul(X("d"), D(2)), Nat())), new Formula.Negate(D(1))),
            At(Local("choiN"), X("N"))))));
    private static Formula ChannelEntropyFormula()
    {
        Formula x = X("x"), y = X("y");
        Formula entry = At(Q("CStarMatrix", "ofMatrix", "symm"), At(
            Seq(X("Q"), Dot, X("toCompletelyPositiveMap")), At(Q("CStarMatrix", "ofMatrix"),
                At(Q("Matrix", "single"), Projection(x, 1), Projection(y, 1), Typed(D(1), Complex())))),
            Projection(x, 2), Projection(y, 2));
        Formula choi = Lambda("x", RightFactor(), Lambda("y", RightFactor(), entry));
        return All("d", Nat(), All("N", MapType(), Equal(At(Local("channelCondMinEntropy"), X("N")),
            new Formula.Negate(Inf("Q", At(Q("QuantumChannel"), Fin(D(2)), Fin(D(2))),
                At(Local("Dmax"), At(Local("choiN"), X("N")), Tensor(One(LeftFactor()), choi)))))));
    }
    private static Formula NoiseFormula()
    {
        Formula matrixU = Typed(X("U"), Matrix(Input()));
        Formula dimension = Typed(Typed(Mul(X("d"), D(2)), Nat()), Complex());
        Formula replacement = S(At(Q("Matrix", "trace"), X("Z")), S(new Formula.Power(dimension, new Formula.Negate(D(1))), One(Input())));
        Formula unitary = Mul(Mul(matrixU, X("Z")), At(Q("star"), matrixU));
        Formula body = Seq(S(X("p"), replacement), Sp, Plus, Sp, S(Seq(D(1), Minus, X("p")), unitary));
        return All("d", Nat(), All("U", At(Q("Matrix", "unitaryGroup"), Input(), Complex()),
            All("p", Real(), All("Z", Matrix(Input()), Equal(At(Local("noisyUnitary"), X("U"), X("p"), X("Z")), body)))));
    }
    private static Formula ClaimBody()
    {
        Formula noisy = At(Local("noisyUnitary"), X("U"), X("p"));
        Formula equality = Equal(At(Local("channelCondMinEntropy"), noisy), Seq(
            At(Local("condMinEntropy"), At(Local("choiState"), noisy)), Sp, Minus, Sp,
            CastEReal(At(Q("Real", "logb"), D(2), CastReal(X("d"))))));
        return All("d", Nat(), ImpliesTo(LeqTo(D(1), X("d")),
            All("U", At(Q("Matrix", "unitaryGroup"), Input(), Complex()), All("p", Real(),
                ImpliesTo(LeqTo(D(0), X("p")), ImpliesTo(LeqTo(X("p"), D(1)), equality))))));
    }
}
