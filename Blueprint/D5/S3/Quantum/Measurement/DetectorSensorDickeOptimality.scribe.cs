using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class DetectorSensorDickeOptimalityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/zhanguptahillery2024detectorsensor");
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Call(V(name), args);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Leqn(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula N => V("n");
    private static Formula FinN => Call("Fin", N);
    private static Formula Word => Fn(FinN, V("Bool"));
    private static Formula State => Fn(Word, Complex);
    private static Formula Povm => Call("LocalPOVM", Word, FinN);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Div(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Slash, Sp, Parenthesized(y));
    private static Formula SumOf(string name, Formula type, Formula body) => Seq(Sum, Sp, V(name), Sp, Colon, Sp, type, Sp, Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Parenthesized(Seq(V("fun"), Sp, V(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Weight(Formula x) => Call(Q("Finset", "card"),
        Call(Q("Finset", "filter"), LambdaOf("j", FinN, Eqn(Call(x, V("j")), V("true"))), Cast(Q("Finset", "univ"), Call("Finset", FinN))));
    private static Formula NormSq(Formula x) => Call(Q("Complex", "normSq"), x);
    private static Formula Choose => Cast(Call(Q("Nat", "choose"), N, V("l")), Real);
    private static Formula PhaseSquare => Seq(V("if"), Sp, Eqn(Weight(V("x")), V("l")), Sp, V("then"), Sp, Div(D(1), Choose), Sp, V("else"), Sp, D(0));
    private static Formula Range => Seq(Parenthesized(Conj(Seq(D(0), Sp, Lt, Sp, V("theta")), Leqn(V("theta"), Call("T", N)))), Sp, Lor, Sp,
        Parenthesized(Conj(Leqn(Sub(Q("Real", "pi"), Call("T", N)), V("theta")), Seq(V("theta"), Sp, Lt, Sp, Q("Real", "pi")))));
    private static Formula Counts(string name, Formula k) => Cast(Call(name, N, Seq(Langle, D(0), Rangle), Seq(Langle, D(1), Rangle), k), Real);
    private static Formula Ratio => Div(Add(Counts("rCount", V("k")), Mul(Call(Q("Real", "cos"), Mul(D(2), V("theta"))), Counts("lCount", V("k")))), Add(Counts("rCount", V("k")), Counts("lCount", V("k"))));
    private static Formula ClaimBody => All("n", Nat, Impl(Leqn(D(3), N), All("theta", Real, Impl(Range,
        All("l", Nat, Impl(Leqn(V("l"), N), Impl(Call("IsMinOn", LambdaOf("k", Nat, Ratio), Call(Q("Set", "Iic"), N), V("l")),
        All("phi", State, Impl(All("x", Word, Eqn(NormSq(Call("phi", V("x"))), PhaseSquare)),
        All("psi", State, Impl(Eqn(SumOf("x", Word, NormSq(Call("psi", V("x")))), D(1)),
        All("M", Povm, Seq(Exists, Sp, Parenthesized(Seq(V("Mp"), Sp, Colon, Sp, Povm)), Sp, Comma, Sp,
            Leqn(Call("isoSuccess", V("theta"), V("psi"), V("M")), Call("isoSuccess", V("theta"), V("phi"), V("Mp"))))))))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced Dicke states maximize the success of equal-prior detector-sensor identification.",
        H("DetectorSensorDickeOptimality"), Blocks(
            Node("fire", FireFormula(), "Section 2, pages 2–3: “Let |𝜙ᵢ⟩ = (𝐼^{⊗𝑖} ⊗ 𝑈 ⊗ 𝐼^{⊗(𝑛−𝑖−1)})|𝜓⟩.” A Boolean word labels the tensor eigenbasis; true is u₊ and false is u₋. Angles are in radians.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("isoSuccess", SuccessFormula(), "Section 2, page 3: “these final states have an equal prior probability”. The success is the mean of the Born probabilities for the correct outcomes. LocalPOVM is the existing finite family of positive semidefinite effects summing to the identity.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("rCount", CountFormula("rCount", Eq), "Section 4, page 7: “For each 0 ≤ 𝑘 ≤ 𝑛, let 𝑅𝑘 be the number of coefficient-squares from 𝑆𝑘 in the RHS of a Real equation”. Observation 1 places a word on this side exactly when its two selected bits agree. The inner cardinality counts the true bits.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("lCount", CountFormula("lCount", Neq), "Section 4, page 7: “𝐿𝑘 be the number of coefficient-squares from 𝑆𝑙 in the LHS of Real equation.” Observation 1 places a word on this side exactly when its two selected bits differ. The source’s Sl in this sentence denotes the selected weight partition.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("T", ThresholdFormula(), "Theorem 2, pages 6–7, defines T = ½ arccos(−(⌈n/2⌉ − 1)/⌈n/2⌉). Nat.div is integer division, so Nat.div (n + 1) 2 is the ceiling of n/2. The outer division is in ℝ.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("claim", Eqn(V("claim"), ClaimBody), "Section 5, Conjecture 1, page 10: “Consider the ISO problem, with the unitary operator 𝑈, initial state |𝜓⟩, and final states {|𝜙ᵢ⟩} as defined therein. Recall that the eigenvalues of 𝑈 are {𝑒^{+𝑖𝜃}, 𝑒^{−𝑖𝜃}}. Let 𝑛 ≥ 3 be the number of sensors. For a given 𝜃 ∈ (0,𝑇] ∪ [180 − 𝑇, 180), degrees, where 𝑇 is from Theorem 2, the optimal initial state |𝜓⟩ for the ISO problem is as follows. Let 𝑆ₗ be the partition that minimizes (𝑅ₗ + cos(2𝜃)𝐿ₗ)/(𝑅ₗ + 𝐿ₗ), where 𝑅ₗ and 𝐿ₗ are as defined in the previous section. The coefficients of the optimal solution are such that their coefficient-squares are given by: |𝜓ⱼ|² = 1/|𝑆ₗ| ∀ |𝜓ⱼ|² ∈ 𝑆ₗ  |𝜓ⱼ|² = 0 ∀ |𝜓ⱼ|² ∉ 𝑆ₗ” The formula uses radians, φ for the proposed state and ψ for a competitor. Each minimizing l and every assignment of coefficient phases are allowed. The words of weight l number Nat.choose n l. The two Fin n indices have values 0 and 1; their proof fields are omitted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("result", V("claim"), "Averaging a feasible Gram decomposition over sensor permutations preserves its objective and produces a real constant overlap. A positive semidefinite trace certificate bounds the objective by the squared diagonal of the Gram square root. This diagonal decreases with the overlap on the stated angle range. Every minimizing weight class reaches the smallest overlap, and a complete square-root measurement attains the bound. The argument allows arbitrary phases and every global POVM; it does not require the source’s stronger strict-averaging Conjecture 2.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Paper)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + "." + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("zhan-gupta-hillery-2024-detector-sensor-dicke-optimality"),
                ResolutionKind.Proved) : null);

    private static Formula FireFormula() => All("n", Nat, All("theta", Real, All("i", FinN, All("psi", State,
        Eqn(Call("fire", V("theta"), V("i"), V("psi")), LambdaOf("x", Word,
            Mul(Call(Q("Complex", "exp"), Mul(Mul(Parenthesized(Seq(V("if"), Sp, Call("x", V("i")), Sp, V("then"), Sp, D(1), Sp, V("else"), Sp, Minus, D(1))), Cast(V("theta"), Complex)), Q("Complex", "I"))), Call("psi", V("x")))))))));
    private static Formula SuccessFormula() => All("n", Nat, All("theta", Real, All("psi", State, All("M", Povm,
        Eqn(Call("isoSuccess", V("theta"), V("psi"), V("M")), Mul(Div(D(1), Cast(N, Real)), SumOf("i", FinN,
            Call(Q("Complex", "re"), Parenthesized(Seq(Call("star", Call("fire", V("theta"), V("i"), V("psi"))), Sp,
                new Formula.Subscript(Cdot, V("v")), Sp, Parenthesized(Seq(Call(Q("LocalPOVM", "effect"), V("M"), V("i")), Sp,
                    new Formula.Subscript(Times, V("v")), Sp, Call("fire", V("theta"), V("i"), V("psi"))))))))))))));
    private static Formula CountFormula(string name, Formula relation) => All("n", Nat, All("i", FinN, All("j", FinN, All("k", Nat,
        Eqn(Call(name, N, V("i"), V("j"), V("k")), Call(Q("Finset", "card"), Call(Q("Finset", "filter"),
            LambdaOf("x", Word, Parenthesized(Conj(Eqn(Weight(V("x")), V("k")), Seq(Call("x", V("i")), Sp, relation, Sp, Call("x", V("j")))))),
            Cast(Q("Finset", "univ"), Call("Finset", Word)))))))));
    private static Formula ThresholdFormula() => All("n", Nat, Eqn(Call("T", N),
        Seq(V("let"), Sp, V("q"), Sp, Colon, Sp, Nat, Sp, Eq, Sp, Call(Q("Nat", "div"), Parenthesized(Add(N, D(1))), D(2)), Sp, V("in"), Sp,
            Div(Call(Q("Real", "arccos"), Seq(Minus, Parenthesized(Div(Sub(Cast(V("q"), Real), D(1)), Cast(V("q"), Real))))), D(2)))));
}
