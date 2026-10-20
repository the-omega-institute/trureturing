using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SeparableWassersteinComparisonRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/toth2026wassersteinfidelities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For two mixed states in dimension four, the modified separable transport cost is at least 15/16, whereas the modified De Palma–Trevisan cost is at most 9/16.",
        H("Modified separable Wasserstein transport can exceed quantum transport"),
        Blocks(
            Node("separableCouplings", "Separable couplings", SeparableCouplingsFormula(),
                "The coupling set uses the marginal convention of Tóth–Pitrik, Section III, equation (GMPC_distance_sep). Here partialTraceLeft is Tr₁, tracing out the first tensor factor, and partialTraceRight is Tr₂, tracing out the second. Thus Tr₁ γ = ρ and Tr₂ γ = σ. IsSeparable means a finite convex mixture γ = Σⱼ pⱼ Aⱼ ⊗ Bⱼ, where pⱼ are nonnegative real numbers summing to one and every Aⱼ and Bⱼ is positive semidefinite with trace one. The additional positivity and trace conditions in the displayed set are retained explicitly.",
                AssessedProvenance.FromLiterature(Source)),
            Node("quantumCostOperator", "The quantum cost operator", CostOperatorFormula(true),
                "Section II, equation (DPT): the transpose is the ordinary matrix transpose in the chosen basis, rather than the conjugate transpose. The function kronecker denotes the tensor product of matrices, and 1 is the identity matrix of the indicated dimension. The factor 1/2 is included in the operator. The index n ranges over Fin N; the definition itself imposes no Hermitian hypothesis.",
                AssessedProvenance.FromLiterature(Source)),
            Node("separableCostOperator", "The separable cost operator", CostOperatorFormula(false),
                "Section III, equation (GMPC_distance_sep): the separable transport cost has no transpose on H n. As in the quantum cost, the factor 1/2 multiplies the sum of squared matrix differences. This operator is defined for every finite complex matrix family.",
                AssessedProvenance.FromLiterature(Source)),
            Node("quantumCost", "The quantum coupling cost", CostFormula(true),
                "The real cost is the real part of the trace of the quantum cost operator times γ. For Hermitian H and a density matrix γ this agrees with the trace objective in equation (DPT); taking the real part makes the definition real valued for arbitrary matrix arguments as well.",
                AssessedProvenance.FromLiterature(Source)),
            Node("separableCost", "The separable coupling cost", CostFormula(false),
                "The real cost is the real part of the trace of the separable cost operator times γ, with the same factor 1/2 as equation (GMPC_distance_sep). Membership in the coupling set is a separate condition, rather than a hypothesis of this cost function.",
                AssessedProvenance.FromLiterature(Source)),
            Node("quantumSquared", "The squared De Palma–Trevisan distance", SquaredFormula(true),
                "Section II, equation (DPT). The displayed coupling set is exactly couplings(ρ,σ): γ is positive semidefinite with trace one, Tr₂ γ = σ, and Tr₁ γ = ρᵀ. The real infimum sInf of the cost image expresses the source's minimization. Here sInf uses the total real-infimum convention, with value zero on empty sets and on sets unbounded below; the infimum estimates below concern nonempty sets bounded below. No square root is taken.",
                AssessedProvenance.FromLiterature(Source)),
            Node("separableSquared", "The squared separable distance", SquaredFormula(false),
                "Section III, equation (GMPC_distance_sep). The real infimum is over separableCouplings(ρ,σ), so its marginals are Tr₁ γ = ρ and Tr₂ γ = σ without a transpose. It uses separableCost, rather than quantumCost. The definition is a real infimum of a cost image, with the same total-infimum convention as quantumSquared.",
                AssessedProvenance.FromLiterature(Source)),
            Node("modifiedQuantumSquared", "The modified quantum squared distance", ModifiedFormula(true),
                "Section II, equation (Dmod): subtract half the sum of the two quantum self-cost infima from the quantum cross-cost infimum. The notation for a modified squared distance names this real expression; it does not square a separately defined function.",
                AssessedProvenance.FromLiterature(Source)),
            Node("modifiedSeparableSquared", "The modified separable squared distance", ModifiedFormula(false),
                "Section III, equation (tildeDPTsep): subtract half the sum of the two separable self-cost infima from the separable cross-cost infimum. Every term uses the separable cost and the untransposed marginal convention.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal comparison in Conjecture 1", ClaimFormula(),
                "Tóth–Pitrik, Conjecture 1, asserts that the modified separable squared distance is at most the modified De Palma–Trevisan squared distance for arbitrary mixed states. Here the assertion ranges over all natural dimensions d and family sizes N, all Hermitian complex matrix families H, and all density matrices ρ and σ. IsDensity means positive semidefinite with trace one. Pure states are included, and no invertibility or strict mixedness assumption is imposed. The literal d = 0 and N = 0 cases are retained in these quantifiers.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A four-dimensional counterexample", Disp(new Formula.Not(Call("claim"))),
                "Take d = 4 and N = 3 in the ordered basis e₀,e₁,e₂,e₃. Set ρ = diag(3,3,1,1)/8 and σ = diag(1,1,3,3)/8. Both are strictly positive density matrices. Let H₁ have rows (0,2,0,0), (2,0,0,0), (0,0,0,1), (0,0,1,0); let H₂ = diag(1,−1,2,−2); and let H₃ = T/4, where T interchanges e₀ with e₂ and e₁ with e₃. These three matrices are real symmetric, so the two cost operators coincide with C = C₀ + (I − T ⊗ T)/16, where C₀ = 5I − H₁ ⊗ H₁ − H₂ ⊗ H₂.\n" +
                "For v in the tensor product write P(v) = |v⟩⟨v|, without normalizing v. Let E be the diagonal projection onto |ij⟩ with i and j in different blocks {0,1} and {2,3}. Put a = |00⟩ − |11⟩, b₀ = |01⟩ − |10⟩, b₁ = |03⟩ − |12⟩, b₂ = |21⟩ − |30⟩, and b₃ = |23⟩ − |32⟩. The decomposable identity C₀ − I − 2E = A + Γ(B) holds with A = 3P(a) + 4P(b₀) + 2P(b₁) + 2P(b₂) + 6P(|23⟩) + 6P(|32⟩) + P(b₃) and B = P(b₀) + 2P(b₁) + 2P(b₂) + P(b₃). Here Γ transposes the second tensor factor. Both A and B are positive semidefinite. Every separable γ has positive partial transpose, so Re Tr((A + Γ(B))γ) ≥ 0. Its marginals give Re Tr(Eγ) = 1/2 + 2 Σᵢ∈{0,1},ⱼ∈{2,3} Re γᵢⱼ,ᵢⱼ ≥ 1/2. The remaining operator (I − T ⊗ T)/16 is positive semidefinite. Consequently every separable cross coupling has cost at least 1 + 2·(1/2) = 2.\n" +
                "For explicit separable self-couplings, take the unit vectors u₀ = (e₀ + e₁)/√2, u₁ = (e₀ − e₁)/√2, u₂ = e₂, and u₃ = e₃. The mixtures Σⱼ wⱼ P(uⱼ) ⊗ P(uⱼ), with weights (3,3,1,1)/8 and (1,1,3,3)/8, have both marginals ρ and both marginals σ, respectively. Each has cost 17/16, hence both separable self-cost infima are at most 17/16.\n" +
                "An explicit quantum cross coupling is P(|00⟩ + |11⟩)/8 + P(|20⟩ + |31⟩)/4 + P(|22⟩ + |33⟩)/8. It has trace one, Tr₁ γ = ρᵀ = ρ, Tr₂ γ = σ, and cost 9/16. The quantum cost operator is positive semidefinite: each Hermitian difference Hₙᵀ ⊗ I − I ⊗ Hₙ has a positive semidefinite square. Thus quantum costs on density matrices, and in particular both quantum self-cost infima, are nonnegative. It follows that the modified separable squared distance is at least 2 − 17/16 = 15/16, while the modified quantum squared distance is at most 9/16. Since 15/16 > 9/16, this pair contradicts Conjecture 1 of Tóth–Pitrik. The matrices, couplings and decomposable bound are the construction here; the distance definitions and conjectured comparison are from the cited source.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("toth-pitrik-2026-separable-wasserstein-comparison-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("tpwasserstein-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(prose.Split('\n')
                .Select(part => Paragraph(Text(part))).ToArray()), role, resolution);

    private static Formula Call(string name, params Formula[] arguments) => arguments.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Iff, Par(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Par(left), FormulaBinaryOperator.Multiply, Par(right));
    private static Formula Fr(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => Call("Fin", size);
    private static Formula Mat(Formula size) => Call("Matrix", FinOf(size), FinOf(size), Complexes());
    private static Formula JointMat(Formula size) => Call("Matrix",
        Par(Seq(FinOf(size), Times, FinOf(size))), Par(Seq(FinOf(size), Times, FinOf(size))), Complexes());
    private static Formula Family(Formula size, Formula count) => Par(new Formula.TypeArrow(FinOf(count), Mat(size)));
    private static Formula SetOf(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Bar, Sp, predicate, CloseBrace);
    private static Formula SumIn(Formula variable, Formula domain, Formula value) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, InMacro, Sp, domain)), Sp, value);
    private static Formula Tr(Formula value) => Call("trace", value);
    private static Formula Transpose(Formula value) => new Formula.Power(Par(value), F.Id("T"));
    private static Formula Density(Formula value) => And(Call("PosSemidef", value), Eq(Tr(value), D(1)));
    private static Formula ForFamily(Formula body) => All(F.Id("d"), Naturals(), All(F.Id("N"), Naturals(),
        All(F.Id("H"), Family(F.Id("d"), F.Id("N")), body)));
    private static Formula ForStates(Formula body) => All(Rho, Mat(F.Id("d")), All(SigmaLower, Mat(F.Id("d")), body));

    private static Formula SeparableCouplingsFormula()
    {
        Formula d = F.Id("d"), g = GammaLower;
        var predicate = And(Density(g), And(Call("IsSeparable", g),
            And(Eq(Call("partialTraceLeft", g), Rho), Eq(Call("partialTraceRight", g), SigmaLower))));
        return Disp(All(d, Naturals(), ForStates(Eq(Call("separableCouplings", Rho, SigmaLower),
            SetOf(g, JointMat(d), predicate)))));
    }

    private static Formula CostOperatorFormula(bool quantum)
    {
        Formula h = F.Id("H"), n = F.Id("n"), hn = new Formula.Apply(h, [n]);
        var difference = Sub(Call("kronecker", quantum ? Transpose(hn) : hn, D(1)),
            Call("kronecker", D(1), hn));
        var value = Seq(Fr(D(1), D(2)), Sp, Cdot, Sp,
            Par(SumIn(n, FinOf(F.Id("N")), new Formula.Power(Par(difference), D(2)))));
        return Disp(ForFamily(Eq(Call(quantum ? "quantumCostOperator" : "separableCostOperator", h), value)));
    }

    private static Formula CostFormula(bool quantum)
    {
        Formula h = F.Id("H"), g = GammaLower;
        var value = Call("re", Tr(Mul(Call(quantum ? "quantumCostOperator" : "separableCostOperator", h), g)));
        return Disp(ForFamily(All(g, JointMat(F.Id("d")),
            Eq(Call(quantum ? "quantumCost" : "separableCost", h, g), value))));
    }

    private static Formula SquaredFormula(bool quantum)
    {
        Formula d = F.Id("d"), h = F.Id("H"), g = GammaLower, r = F.Id("r");
        var couplings = quantum
            ? SetOf(g, JointMat(d), And(Density(g), And(Eq(Call("partialTraceRight", g), SigmaLower),
                Eq(Call("partialTraceLeft", g), Transpose(Rho)))))
            : Call("separableCouplings", Rho, SigmaLower);
        var costs = SetOf(r, Reals(), Some(g, JointMat(d), And(Mem(g, couplings),
            Eq(r, Call(quantum ? "quantumCost" : "separableCost", h, g)))));
        return Disp(ForFamily(ForStates(Eq(Call(quantum ? "quantumSquared" : "separableSquared", h, Rho, SigmaLower),
            Call("sInf", costs)))));
    }

    private static Formula ModifiedFormula(bool quantum)
    {
        Formula h = F.Id("H");
        string squared = quantum ? "quantumSquared" : "separableSquared";
        var value = Sub(Call(squared, h, Rho, SigmaLower),
            Fr(Add(Call(squared, h, Rho, Rho), Call(squared, h, SigmaLower, SigmaLower)), D(2)));
        return Disp(ForFamily(ForStates(Eq(Call(quantum ? "modifiedQuantumSquared" : "modifiedSeparableSquared",
            h, Rho, SigmaLower), value))));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("H"), n = F.Id("n");
        var hermitian = All(n, FinOf(F.Id("N")), Call("IsHermitian", new Formula.Apply(h, [n])));
        var inequality = Le(Call("modifiedSeparableSquared", h, Rho, SigmaLower),
            Call("modifiedQuantumSquared", h, Rho, SigmaLower));
        var assertion = ForFamily(Imp(hermitian, ForStates(Imp(Call("IsDensity", Rho),
            Imp(Call("IsDensity", SigmaLower), inequality)))));
        return Disp(IffTo(Call("claim"), assertion));
    }
}
