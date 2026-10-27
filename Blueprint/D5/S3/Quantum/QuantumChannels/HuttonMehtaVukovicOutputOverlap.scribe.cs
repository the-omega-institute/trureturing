using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class HuttonMehtaVukovicOutputOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/huttonmehtavukovic2025cqoverlap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal pure inputs to a classical–quantum channel have average output overlap at least the minimum over distinct basis inputs.",
        H("The minimum overlap of orthogonal channel inputs"),
        Blocks(
            Paragraph(Text("Matrices have complex entries. Fin n indexes the source's n computational basis vectors from zero; sigma is the family of output states, and u lists the input vectors. Products and traces are matrix products and Matrix.trace. Complex.re gives the real comparison. The sums over r and s count ordered pairs, with zero diagonal terms.")),
            Node("state", "Quantum states", StateFormula(), "IsState",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "A quantum state in M_d(ℂ) is a positive semidefinite matrix with trace one."),
            Node("output", "Output on a pure input", OutputFormula(), "channelOutput",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Definition 1.3, page 2: “A C–Q channel Φ from an n-qubit space to an m-qubit space is specified by 2ⁿ states σ₁, …, σ_{2ⁿ} on m qubits and acts as Φ(ρ) = Σᵢ Tr(|i⟩⟨i| ρ) σᵢ.” On a pure input, the coefficient is the squared modulus of its i-th coordinate. The formula below permits every finite input and output dimension."),
            Node("orthonormal", "Orthonormal input families", OrthonormalFormula(), "IsOrthonormalFamily",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "The vectors u₁, …, u_k are pairwise orthogonal pure states, or unit vectors, in ℂⁿ. Their coordinate inner products are one on the diagonal and zero off the diagonal."),
            Node("average", "Average output overlap", AverageFormula(), "averageOutputOverlap",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "The left side of Conjecture 1.5, page 3, divides the sum over ordered unequal pairs by k(k−1). The displayed reciprocal and products are in the real numbers. The definition exists for every k; the theorem assumes k is at least two."),
            Node("minimum", "Minimum over distinct basis inputs", MinimumFormula(), "minDistinctOverlap",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "The right side of Conjecture 1.5, page 3, minimizes over k distinct basis indices. An injective map from Fin k to Fin n specifies the ordered list. Since the set of such maps is finite and is nonempty when k ≤ n, its real infimum is its minimum. Subtype.val extracts this injective map."),
            Node("claim", "Conjecture 1.5", Disp(IffOf(Qualified("claim"), ClaimBody())), "claim",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Conjecture 1.5, page 3: “Let σ₁, …, σₙ ∈ M_d(ℂ) be arbitrary quantum states. Then for any collection of k ≤ n of pairwise orthogonal pure states |u₁⟩, …, |u_k⟩ ∈ ℂⁿ, the following bound holds: (1/(k(k−1))) Σ_{r≠s} Tr((Σᵢ |⟨i|u_r⟩|² σᵢ)(Σⱼ |⟨j|u_s⟩|² σⱼ)) ≥ min_{i₁,…,i_k ∈ [n] distinct} (1/(k(k−1))) Σ_{r≠s} Tr(σ_{i_r} σ_{i_s}).” A quantum state is positive semidefinite with trace one. The coordinate inner-product equality expresses that the pure input vectors have norm one and are pairwise orthogonal. The real reciprocal requires 2 ≤ k."),
            Node("result", "The orthogonal lower bound", Disp(ClaimBody()), "result",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "The squared absolute determinants of the k-row minors of the input matrix form a probability distribution on k-element subsets, by Cauchy–Binet and orthonormality. Its average subset overlap is at least the minimum subset overlap. The difference between the total output overlap and this average is a sum of traces of products TᴴT, where T is the cross combination Σᵢ conj(Uᵢᵣ)Uᵢₛσᵢ. Each term is nonnegative. Dividing by the positive real number k(k−1) gives the inequality. The residual identity uses Hermiticity; no non-orthogonal correction is asserted.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hutton-mehta-vukovic-2025-cq-output-overlap-minimum"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string declaration, DescribeRole role, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hmv-output-overlap-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string name)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Qualified(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), Field("C"));
    private static Formula Fun(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Parenthesized(Seq(V(name), Colon, type))), Sp, Parenthesized(body));
    private static Formula Coefficient()
    {
        var k = Parenthesized(Seq(V("k"), Colon, Field("R")));
        return new Formula.Fraction(D(1), Mul(k,
            new Formula.Binary(k, FormulaBinaryOperator.Subtract, D(1))));
    }
    private static Formula UnequalPair(Formula body) =>
        Call("ite", EqOf(V("r"), V("s")), D(0), body);
    private static Formula PairSum(Formula body) =>
        SumOver("r", Fin(V("k")), SumOver("s", Fin(V("k")), UnequalPair(body)));
    private static Formula TraceReal(Formula a, Formula b) => Call("Complex.re", Call("Matrix.trace", Mul(a, b)));
    private static Formula StateType() => Fun(Fin(V("n")), Mat(V("d")));
    private static Formula InputType() => Fun(Fin(V("k")), Fun(Fin(V("n")), Field("C")));
    private static Formula Parameters(Formula body, bool includeK) =>
        All("n", Field("N"), All("d", Field("N"), includeK ? All("k", Field("N"), body) : body));
    private static Formula StateFormula() =>
        Disp(All("d", Field("N"), All("sigma", Mat(V("d")),
            IffOf(Call("IsState", V("sigma")),
                AndOf(Call("Matrix.PosSemidef", V("sigma")),
                    EqOf(Call("Matrix.trace", V("sigma")), D(1)))))));
    private static Formula OrthonormalFormula()
    {
        Formula inner = SumOver("i", Fin(V("n")), Mul(Call("star", At(V("u"), V("r"), V("i"))),
            At(V("u"), V("s"), V("i"))));
        Formula delta = Call("ite", EqOf(V("r"), V("s")), D(1), D(0));
        return Disp(All("n", Field("N"), All("k", Field("N"), All("u", InputType(),
            IffOf(Call("IsOrthonormalFamily", V("u")),
                All("r", Fin(V("k")), All("s", Fin(V("k")), EqOf(inner, delta))))))));
    }
    private static Formula OutputFormula()
    {
        Formula coefficient = Call("Complex.ofReal", Call("Complex.normSq", At(V("u"), V("i"))));
        Formula sum = SumOver("i", Fin(V("n")), Call("HSMul.hSMul", coefficient, At(V("sigma"), V("i"))));
        return Disp(Parameters(All("sigma", StateType(), All("u", Fun(Fin(V("n")), Field("C")),
            EqOf(Call("channelOutput", V("sigma"), V("u")), sum))), false));
    }
    private static Formula AverageFormula()
    {
        Formula r = Call("channelOutput", V("sigma"), At(V("u"), V("r")));
        Formula s = Call("channelOutput", V("sigma"), At(V("u"), V("s")));
        return Disp(Parameters(All("sigma", StateType(), All("u", InputType(),
            EqOf(Call("averageOutputOverlap", V("sigma"), V("u")), Mul(Coefficient(), PairSum(TraceReal(r, s)))))), true));
    }
    private static Formula MinimumFormula()
    {
        Formula injectionType = Seq(OpenBrace, Sp, V("j"), Colon, Fun(Fin(V("k")), Fin(V("n"))), Sp,
            Slash, Slash, Sp, Call("Function.Injective", V("j")), Sp, CloseBrace);
        Formula indexMap = Call("Subtype.val", V("iota"));
        Formula score = Mul(Coefficient(), PairSum(TraceReal(
            At(V("sigma"), At(indexMap, V("r"))), At(V("sigma"), At(indexMap, V("s"))))));
        Formula infimum = Seq(new Formula.Subscript(Qualified("iInf"), Parenthesized(Seq(V("iota"), Colon, injectionType))), Sp, Parenthesized(score));
        return Disp(Parameters(All("sigma", StateType(), All("k", Field("N"),
            EqOf(Call("minDistinctOverlap", V("sigma"), V("k")), infimum))), false));
    }
    private static Formula ClaimBody()
    {
        Formula states = All("i", Fin(V("n")), Call("IsState", At(V("sigma"), V("i"))));
        Formula orthonormal = Call("IsOrthonormalFamily", V("u"));
        Formula conclusion = LeOf(Call("minDistinctOverlap", V("sigma"), V("k")),
            Call("averageOutputOverlap", V("sigma"), V("u")));
        return Parameters(All("sigma", StateType(), ImpliesOf(states,
            ImpliesOf(LeOf(D(2), V("k")), ImpliesOf(LeOf(V("k"), V("n")),
                All("u", InputType(), ImpliesOf(orthonormal, conclusion)))))), true);
    }
}
