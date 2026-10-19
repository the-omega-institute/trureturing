using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class GaussianAtemporalityEntanglementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/GaussianAtemporalityEntanglement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/song2025gaussianatemporality");
    private const string StandardQuote = "Definition 1, p. 3: \"Let Alice and Bob each have access to a qumode with standard basis (q̂_A,p̂_A) and (q̂_B,p̂_B), with locally diagonal covariance matrices V_A and V_B.\" VA and VB are real matrices indexed by Fin 2; Matrix.IsDiag expresses locally diagonal covariance matrices.";
    private const string AtemporalQuote = "Section III.B, p. 4: \"We then say that V_AB is Gaussian atemporal if it is Gaussian-atemporal in both temporal direction.\" The two negated Matrix.PosSemidef predicates express failure of the two channel complete-positivity inequalities.";
    private const string ClaimQuote = "Section III.D, p. 6: \"From Fig. 3, Gaussian-atemporality appears to imply entanglement. The converse, on the other hand is not generally true.\" The quantifiers range over all real two-by-two local blocks VA, VB and cross block C, in quadrature order (q_A,p_A,q_B,p_B), with ℏ = 2. Standard form means locally diagonal blocks. IsSpatiallyPhysical is the uncertainty inequality; IsGaussianAtemporal requires incompatibility in both directions; IsEntangled is failure of the partially transposed uncertainty inequality, the two-mode Gaussian PPT test used by the source.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive partial transpose implies temporal compatibility in both directions for physical two-mode Gaussian covariance matrices; Gaussian atemporality therefore implies entanglement in the covariance PPT formulation.",
        H("Gaussian atemporality implies entanglement"),
        Blocks(
            Node("covariance", "Space-time covariance matrix", Disp(Three(Eq(
                Cov(), Call("Matrix.fromBlocks", A, C, Transpose(C), B)))),
                "Equation (2), p. 3, is V_AB = [[V_A,C],[Cᵀ,V_B]]. The Sum index lists Alice's two quadratures before Bob's two quadratures.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsStandardForm", "Locally diagonal covariance matrices", Disp(All("VA", RealMatrix(),
                All("VB", RealMatrix(), Iff(Call("IsStandardForm", A, B),
                    And(Call("Matrix.IsDiag", A), Call("Matrix.IsDiag", B)))))),
                StandardQuote, DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSpatiallyPhysical", "The spatial uncertainty inequality", Disp(Three(Iff(
                Call("IsSpatiallyPhysical", A, B, C), Psd(Uncertainty(Cov()))))),
                "The real covariance matrix obeys the uncertainty principle V_AB + i(Ω ⊕ Ω) ≥ 0, with ℏ = 2. Matrix.PosSemidef includes Hermiticity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("forwardX", "Forward atemporality matrix", ForwardFormula(),
                "Equations (7) and (8), p. 4: T = Cᵀ V_A⁻¹, N = V_B − Cᵀ V_A⁻¹ C and X(T,N) ≡ N + iΩ − iTΩTᵀ. Inv.inv uses the total nonsingular matrix inverse; physicality ensures that the local blocks are invertible.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsGaussianAtemporal", "Incompatibility in both directions", Disp(Three(Iff(
                Call("IsGaussianAtemporal", A, B, C), And(
                    new Formula.Not(Psd(Call("forwardX", A, B, C))),
                    new Formula.Not(Psd(Call("forwardX", B, A, Transpose(C)))))))),
                AtemporalQuote, DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("partialTransposeA", "Partial transpose on Alice", PartialTransposeFormula(),
                "Partial transposition on Alice flips p_A. In the real covariance matrix it acts by Λ V_AB Λ, with Λ = diag(1,−1,1,1); Matrix.diagonal ![1,−1] is Alice's momentum flip.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsEntangled", "The two-mode Gaussian PPT entanglement test", Disp(Three(Iff(
                Call("IsEntangled", A, B, C), new Formula.Not(Psd(Uncertainty(
                    Call("partialTransposeA", A, B, C))))))),
                "Section III.D, p. 5, uses the positive partial transpose criterion. This predicate is failure of the partially transposed uncertainty inequality. Its interpretation as entanglement uses the source's two-mode Gaussian PPT criterion; a Hilbert-space separability theorem is outside the matrix statement.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The entanglement assertion", Disp(Iff(X("claim"), ClaimBody())), ClaimQuote,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Gaussian atemporality implies entanglement", Disp(ClaimBody()),
                "A physical local uncertainty matrix has strictly positive real covariance: a null quadratic form would annihilate its vector, whose imaginary part then forces Ωx = 0. Thus both local blocks are invertible. Conjugating the PPT inequality by the momentum flip gives H = V_AB + i((−Ω) ⊕ Ω) positive semidefinite. With T = Cᵀ VA⁻¹ and K = [−T,1], matrix multiplication gives K V_AB Kᵀ = N and K((−Ω) ⊕ Ω)Kᵀ = Ω − TΩTᵀ. Congruence yields forwardX positive semidefinite. Complex conjugation and exchange of Alice and Bob give the reverse direction. Either directional incompatibility therefore contradicts PPT. Diagonality of the local blocks is unnecessary for this argument.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gaussian-atemporality-entanglement"),
                    ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("gaussian-atemporality-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula A => X("VA");
    private static Formula B => X("VB");
    private static Formula C => X("C");
    private static Formula Named(string name)
    {
        var parts = name.Split('.');
        var tokens = new List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) tokens.Add(Dot);
            tokens.Add(X(parts[i]));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Three(Formula body) => All("VA", RealMatrix(), All("VB", RealMatrix(), All("C", RealMatrix(), body)));
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula FinTwo() => Call("Fin", D(2));
    private static Formula RealMatrix() => Call("Matrix", FinTwo(), FinTwo(), Reals());
    private static Formula Transpose(Formula matrix) => Call("Matrix.transpose", matrix);
    private static Formula Cov() => Call("covariance", A, B, C);
    private static Formula Complexify(Formula matrix) => Call("Matrix.map", matrix, Named("Complex.ofReal"));
    private static Formula Psd(Formula matrix) => Call("Matrix.PosSemidef", Parenthesized(matrix));
    private static Formula SmulI(Formula matrix) => Call("SMul.smul", Named("Complex.I"), Complexify(matrix));
    private static Formula Uncertainty(Formula matrix) => Add(Complexify(matrix),
        SmulI(Call("Matrix.fromBlocks", Named("D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2"), D(0), D(0), Named("D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2"))));
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Seq(
        Named("let"), Sp, X(name), Colon, type, Colon, F.Eq, Parenthesized(value), Semi, Sp, body);

    private static Formula ForwardFormula()
    {
        Formula t = X("T"), n = X("N");
        Formula trans = Mul(Transpose(C), Call("Inv.inv", A));
        Formula noise = Sub(B, Mul(Mul(Transpose(C), Call("Inv.inv", A)), C));
        Formula body = Sub(Add(Complexify(n), SmulI(Named("D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2"))), SmulI(Mul(Mul(t, Named("D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2")), Transpose(t))));
        return Disp(Three(Eq(Call("forwardX", A, B, C),
            Let("T", RealMatrix(), trans, Let("N", RealMatrix(), noise, body)))));
    }
    private static Formula PartialTransposeFormula()
    {
        Formula sum = Call("Sum", FinTwo(), FinTwo());
        Formula lambdaType = Call("Matrix", sum, sum, Reals());
        Formula flip = Call("Matrix.diagonal", Seq(Bang, OpenBracket, D(1), Comma, new Formula.Negate(D(1)), CloseBracket));
        return Disp(Three(Eq(Call("partialTransposeA", A, B, C), Let("Lambda", lambdaType,
            Call("Matrix.fromBlocks", flip, D(0), D(0), D(1)), Mul(Mul(X("Lambda"), Cov()), X("Lambda"))))));
    }
    private static Formula ClaimBody() => Three(Imp(Call("IsStandardForm", A, B),
        Imp(Call("IsSpatiallyPhysical", A, B, C), Imp(Call("IsGaussianAtemporal", A, B, C),
            Call("IsEntangled", A, B, C)))));
}
