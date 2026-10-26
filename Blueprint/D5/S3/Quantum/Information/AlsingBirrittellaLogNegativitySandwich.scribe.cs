using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class AlsingBirrittellaLogNegativitySandwichDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/alsingbirrittella2024lognegativity");
    private const string SourceQuote = "we have numerically found that 𝓛𝓝_a^avg(ρ_ab) ≤ LN_e(ρ_ab) ≤ LN_a(ρ_ab) when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|, and in addition the quantum amplitude matrix C_i of each pure state component |ψ_i⟩ = Σ_nm C_i,nm |n,m⟩ is uniformly generated (over the Haar measure) as a positive Hermitian matrix, C_i = C_i† ≥ 0.";
    private const string RealQuote = "Further, we find that the second inequality is surprisingly saturated, i.e. LN_e(ρ_ab) = LN_a(ρ_ab) in Eq.(22), if the uniformly randomly generated C_i matrices above are real, i.e. C_i = C_i^T.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Hermitian amplitude matrices give an exact trace-norm formula, a logarithmic-negativity sandwich, and equality of the upper bound for real amplitudes.",
        H("The Alsing–Birrittella logarithmic-negativity sandwich"),
        Blocks(
            Node("ensembleState", "The finite pure-state ensemble", EnsembleFormula(),
                "Alsing and Birrittella, arXiv:2404.13725v1, p. 11: \"when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|\". Here d is the subsystem dimension and K is the ensemble size. Function.uncurry C maps (n,m) to C n m, so Matrix.vecMulVec forms the pure-state outer product. Each real weight is embedded in ℂ before scalar multiplication.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("exactLogNegativity", "Exact logarithmic negativity in bits", ExactFormula(),
                "Introduction, p. 1: \"A widely used “measure” of entanglement for both pure and mixed states, both discrete and continuous variable, is the Log Negativity (LN)\", given by LN(ρ_ab) = log₂(1 + 2 N), \"where the negativity N is given by the sum of the absolute values of the negative eigenvalues of the partial transpose of ρ_ab.\" Here the exact logarithmic negativity is expressed as log₂ ‖ρ^Γ‖₁. KickedIsingNegativityRefutation.partialTranspose transposes the second tensor factor: its (a,b),(c,e) entry is ρ(a,e),(c,b). FiniteTraceDistance.traceNorm is the real part of the trace of CFC.sqrt (X adjoint times X). Real.logb uses base two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pureApproxNegativity", "The pure-state determinant expression", PureNegativityFormula(),
                "Equation (11a), p. 4: N_a(|ψ⟩_ab) := ½ Σ_n Σ_(m≠n) |Det [[c_nn,c_nm],[c_mn,c_mm]]|. Both sums run over Fin d. The expression is half the sum over ordered unequal pairs; diagonal terms are zero. The complex norm is the absolute value of the displayed two-by-two determinant.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pureApproxLogNegativity", "The pure-state logarithmic expression", PureLogFormula(),
                "Equation (11b), p. 4: LN_a(|ψ⟩_ab) := log₂(1 + 2 N_a(|ψ⟩_ab)). The logarithm is applied after summing the determinant absolute values.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mixedApproxNegativity", "The mixed-state entry expression", MixedNegativityFormula(),
                "Equation (17b), p. 8: N_a → ½ Σ_(n,m≠n) |ρ_nn,mm − ρ_nm,mn|. The factor one half and ordered unequal-pair summation are retained, with zero on the diagonal.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mixedApproxLogNegativity", "The mixed-state logarithmic expression", MixedLogFormula(),
                "Equation (17c), p. 8: LN_a = log₂(1 + 2 N_a). This uses the mixed-state entry expression of Equation (17b).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The sandwich and its real-amplitude equality", Disp(IffTo(F.Id("claim"), ClaimBody())),
                "Section IV, p. 11, Equation (22): \"" + SourceQuote + "\" \"" + RealQuote + "\" The quantifiers cover every finite dimension and finite ensemble, including zero weights and singular positive semidefinite amplitudes. Normalization is trace(C_i C_i adjoint) = 1 and Σ_i p_i = 1. Under Hermitian symmetry, transpose(C_i) = C_i expresses real entries. The average on the left is the weighted average of the pure-state logarithmic expression, rather than the logarithm of the averaged negativity. Universal quantification over the positive Hermitian class includes the source's randomly sampled class.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full sandwich holds", Disp(ClaimBody()),
                "Let F be the swap and Q = Σ_i p_i (C_i tensor C_i). The partial transpose of the ensemble is QF; Q is positive semidefinite and commutes with F, and F is a self-adjoint involution. Consequently its trace norm is trace Q = Σ_i p_i (Re trace C_i)². Nonnegative principal two-by-two minors give 1 + 2 N_a(C_i) = (Re trace C_i)². Concavity of the base-two logarithm gives the lower bound. For the upper bound, the real part of each mixed entry difference dominates the weighted nonnegative principal minors, and the complex norm dominates its real part. For transpose-symmetric amplitudes, these comparisons become equalities. No commutativity between different C_i is assumed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("alsing-birrittella-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("alsing-birrittella-2024-log-negativity-sandwich"),
                ResolutionKind.Proved) : null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(name.Split('.').SelectMany((part, index) => index == 0
            ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula PairIndex(Formula d) => Parenthesized(Seq(Fin(d), Times, Fin(d)));
    private static Formula Matrix(Formula index) => Call("Matrix", index, index, Complexes);
    private static Formula Amplitudes(Formula d) => Matrix(Fin(d));
    private static Formula Density(Formula d) => Matrix(PairIndex(d));
    private static Formula Weights(Formula k) => new Formula.TypeArrow(Fin(k), Reals);
    private static Formula Family(Formula d, Formula k) => new Formula.TypeArrow(Fin(k), Amplitudes(d));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Log(Formula value) => Call("Real.logb", D(2), value);
    private static Formula Shifted(Formula value) => Add(D(1), Mul(D(2), value));

    private static Formula EnsembleFormula()
    {
        Formula d = F.Id("d"), k = F.Id("K"), p = F.Id("p"), c = F.Id("C"), i = F.Id("i");
        var vector = Call("Function.uncurry", At(c, i));
        var projector = Call("Matrix.vecMulVec", vector, Call("star", vector));
        var summand = Seq(Call("Complex.ofReal", At(p, i)), Cdot, Sp, projector);
        return Disp(All("d", Naturals, All("K", Naturals, All("p", Weights(k),
            All("C", Family(d, k), EqTo(Call("ensembleState", p, c), Sum("i", Fin(k), summand)))))));
    }

    private static Formula ExactFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho");
        return Disp(All("d", Naturals, All("rho", Density(d), EqTo(Call("exactLogNegativity", rho),
            Log(Call("D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm",
                Call("D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose", rho)))))));
    }

    private static Formula PureNegativityFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C"), n = F.Id("n"), m = F.Id("m");
        var determinant = Sub(Mul(At(c, n, n), At(c, m, m)), Mul(At(c, n, m), At(c, m, n)));
        var summand = Call("ite", EqTo(m, n), D(0), new Formula.Norm(determinant));
        return Disp(All("d", Naturals, All("C", Amplitudes(d), EqTo(Call("pureApproxNegativity", c),
            Mul(new Formula.Fraction(D(1), D(2)), Sum("n", Fin(d), Sum("m", Fin(d), summand)))))));
    }

    private static Formula PureLogFormula()
    {
        Formula d = F.Id("d"), c = F.Id("C");
        return Disp(All("d", Naturals, All("C", Amplitudes(d), EqTo(Call("pureApproxLogNegativity", c),
            Log(Shifted(Call("pureApproxNegativity", c)))))));
    }

    private static Formula MixedNegativityFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho"), n = F.Id("n"), m = F.Id("m");
        var difference = Sub(At(rho, Pair(n, n), Pair(m, m)), At(rho, Pair(n, m), Pair(m, n)));
        var summand = Call("ite", EqTo(m, n), D(0), new Formula.Norm(difference));
        return Disp(All("d", Naturals, All("rho", Density(d), EqTo(Call("mixedApproxNegativity", rho),
            Mul(new Formula.Fraction(D(1), D(2)), Sum("n", Fin(d), Sum("m", Fin(d), summand)))))));
    }

    private static Formula MixedLogFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho");
        return Disp(All("d", Naturals, All("rho", Density(d), EqTo(Call("mixedApproxLogNegativity", rho),
            Log(Shifted(Call("mixedApproxNegativity", rho)))))));
    }

    private static Formula ClaimBody()
    {
        Formula d = F.Id("d"), k = F.Id("K"), p = F.Id("p"), c = F.Id("C"), i = F.Id("i");
        var ci = At(c, i);
        var positivity = All("i", Fin(k), LeTo(D(0), At(p, i)));
        var normalization = EqTo(Sum("i", Fin(k), At(p, i)), D(1));
        var matrices = All("i", Fin(k), Both(Call("Matrix.PosSemidef", ci),
            EqTo(Call("Matrix.trace", Mul(ci, Call("Matrix.conjTranspose", ci))), D(1))));
        var rho = Call("ensembleState", p, c);
        var exact = Call("exactLogNegativity", rho);
        var upper = Call("mixedApproxLogNegativity", rho);
        var lower = Sum("i", Fin(k), Mul(At(p, i), Call("pureApproxLogNegativity", ci)));
        var real = All("i", Fin(k), EqTo(Call("Matrix.transpose", ci), ci));
        var conclusion = Both(Both(LeTo(lower, exact), LeTo(exact, upper)), Imp(real, EqTo(exact, upper)));
        return Parenthesized(All("d", Naturals, All("K", Naturals, All("p", Weights(k), All("C", Family(d, k),
            Imp(positivity, Imp(normalization, Imp(matrices, conclusion))))))));
    }
}
