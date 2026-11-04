using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class EnergyConstrainedDeterministicViolationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/davinoetal2025energyconstrained");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qubit channels give a strict deterministic-input violation of the separable energy bound for every positive energy budget below one half.",
        H("Deterministic violations under an energy constraint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("probability"),
                DeclarationHandle.Create(Module + ".probability"),
                H("The local-channel Born functional"),
                StatementSource.FromAuthor(Disp(ProbabilityDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Apply the channel selected by x to the preparation subsystem of sigma, "
                    + "leave the memory subsystem unchanged, and pair the resulting matrix with "
                    + "the effect selected by b. The value is the real part of this Born trace. "
                    + "The definition accepts arbitrary complex matrices and linear matrix maps; "
                    + "positivity and normalization are imposed in the next statement. This is "
                    + "the two-input, single-measurement specialization of the source's probability "
                    + "formula, TeX lines 137–139 and 148."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Strict violation at every positive energy budget"),
                StatementSource.FromAuthor(Disp(Equal(Named("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For each real energy budget strictly between zero and one half, choose "
                    + "finite preparation, transmitted and memory dimensions, a density matrix, "
                    + "two completely positive trace-preserving maps and a binary positive "
                    + "measurement. The Hermitian Hamiltonian annihilates a unit vector g and "
                    + "dominates the orthogonal complement of its rank-one projector, expressing "
                    + "a unique ground state at energy zero and a gap of at least one. Both "
                    + "prepared states satisfy the energy budget. Input zero gives outcome zero "
                    + "with certainty, while the input-one correlator lies strictly below the "
                    + "separable bound. These are the finite-dimensional conditions corresponding "
                    + "to the source's energy assumptions at TeX lines 151–154, correlator at "
                    + "165–166, inequality at 266–270 and conjecture at 284. The statement requires "
                    + "the displayed state, channel and measurement conditions; it does not "
                    + "include a separate separability predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A qubit construction for the whole open interval"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix 0 < ω < 1/2 and set t = (1 − 2ω)/8. Then 0 < t < 1/8. "
                        + "Choose the positive square roots s = √(1 − ω), "
                        + "r = √(ω(1/2 − t)), q = √(ω(1/2 + t)), "
                        + "a = √(1 − ω − 2ωt) and h = √(2ωt). Their radicands are positive, "
                        + "and they satisfy s² = 1 − ω, r² + q² = ω, q² − r² = h² and "
                        + "a² + h² = s².")),
                    Paragraph(Text(
                        "Take all three systems to have dimension two. In the ordered tensor "
                        + "basis 00, 01, 10, 11, let ψ have coordinates (s, 0, r, q), and let "
                        + "σ = |ψ⟩⟨ψ|. The identity s² + r² + q² = 1 makes σ positive "
                        + "semidefinite with trace one and σ² = σ.")),
                    Paragraph(Text(
                        "For input zero use Kraus matrices I and 0. For input one use "
                        + "K₀ = [[−a/s, 0], [h²/(sq), r/q]] and "
                        + "K₁ = [[−hr/(sq), h/q], [0, 0]]. All entries are complex embeddings "
                        + "of the indicated real quantities. Since s and q are nonzero, direct "
                        + "matrix multiplication using q² − r² = h² and a² + h² = s² gives "
                        + "K₀†K₀ + K₁†K₁ = I. The Kraus sums consequently define completely "
                        + "positive trace-preserving maps for both inputs.")),
                    Paragraph(Text(
                        "Choose the Hamiltonian coordinateProjectorTwo(1), namely diag(0,1), "
                        + "and the ground vector evenChannelState, namely (1,0). The Hamiltonian "
                        + "is Hermitian, the ground vector has squared norm one, and their "
                        + "matrix-vector product is zero. The Hamiltonian equals "
                        + "I − |g⟩⟨g|, so its required positive semidefinite difference is zero. "
                        + "Computing the partial trace of σ and applying each Kraus sum gives "
                        + "the same energy r² + q² = ω for each input.")),
                    Paragraph(Text(
                        "Thus the effects σ and I − σ are positive semidefinite and sum to the identity.")),
                    Paragraph(Text(
                        "For the joint output, amplification by the identity applies the "
                        + "channel to each matrix slice with the memory indices fixed. Evaluating "
                        + "these slices gives σ for input zero. For input one the output is "
                        + "|v⟩⟨v| + h²|01⟩⟨01|, where v has coordinates (−a, 0, q, r). "
                        + "Taking the traces against the two effects gives p(0|0) = 1, "
                        + "p(0|1) = (sa − 2rq)² and p(1|1) = 1 − (sa − 2rq)². In particular, "
                        + "the extra |01⟩ component is orthogonal to ψ; the rank-one trace "
                        + "overlap is the squared modulus of their inner product.")),
                    Paragraph(Text(
                        "To obtain the strict estimate, put x = sa and y = 2rq. Their squares "
                        + "are x² = (1 − ω)(1 − ω − 2ωt) and y² = ω²(1 − 4t²). "
                        + "Comparison of nonnegative squares gives x ≥ 1 − ω − 2ωt, "
                        + "y ≤ ω, x < 1 − ω − ωt and y ≥ ω(1 − 4t²). The first pair yields "
                        + "x − y ≥ (1 − 2ω)(1 − ω/4) > 0. The second pair yields "
                        + "x − y < 1 − 2ω − ωt(1 − 4t) < 1 − 2ω. Squaring therefore gives "
                        + "(sa − 2rq)² < (1 − 2ω)².")),
                    Paragraph(Text(
                        "These matrices and maps satisfy every positivity, trace, ground-state, "
                        + "gap and energy condition in the statement. Finally, subtracting the "
                        + "two input-one probabilities gives 2(sa − 2rq)² − 1, which is strictly "
                        + "less than 2(1 − 2ω)² − 1 by the square-root estimate. The construction "
                        + "therefore supplies the required dimensions and objects for every "
                        + "energy budget in the open interval."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("davino-et-al-2025-energy-constrained-deterministic-violation"),
                    ResolutionKind.Proved)))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula FinOf(Formula size) => At(Named("Fin"), size);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula MatrixOf(Formula indices) => At(Named("Matrix"), indices, indices, Complexes);
    private static Formula MatrixMapOf(Formula input, Formula output) =>
        At(Named("MatrixMap"), input, output, Complexes);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => All(X(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Conjunction(params Formula[] items)
    {
        var body = items[^1];
        for (var index = items.Length - 2; index >= 0; index--) body = And(items[index], body);
        return body;
    }
    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(Parenthesized(hypothesis), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Psd(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula StarOf(Formula value) => At(Named("star"), value);
    private static Formula RealPart(Formula value) => At(Qualified("Complex", "re"), value);
    private static Formula Probability(Formula b, Formula x) =>
        At(Named("probability"), X("sigma"), X("lam"), X("povm"), b, x);
    private static Formula ProbabilityDefinition()
    {
        Formula dp = FinOf(X("dp")), ds = FinOf(X("ds")), dm = FinOf(X("dm"));
        Formula identity = Typed(Qualified("LinearMap", "id"), MatrixMapOf(dm, dm));
        Formula image = At(Qualified("MatrixMap", "kron"), At(X("lam"), X("x")), identity, X("sigma"));
        Formula born = At(Qualified("FiniteDimensional", "bornProbability"), At(X("povm"), X("b")), image);
        return All("dp", Naturals, All("ds", Naturals, All("dm", Naturals,
            All("sigma", MatrixOf(Product(dp, dm)),
            All("lam", Arrow(FinOf(D(2)), MatrixMapOf(dp, ds)),
            All("povm", Arrow(FinOf(D(2)), MatrixOf(Product(ds, dm))),
            All("b", FinOf(D(2)), All("x", FinOf(D(2)),
                Equal(Probability(X("b"), X("x")), RealPart(born))))))))));
    }

    private static Formula ClaimBody()
    {
        Formula dp = FinOf(X("dp")), ds = FinOf(X("ds")), dm = FinOf(X("dm"));
        Formula local = At(X("lam"), X("x"));
        Formula channels = All("x", FinOf(D(2)), And(
            At(Qualified("MatrixMap", "IsCompletelyPositive"), local),
            All("rho", MatrixOf(dp), Equal(Trace(At(local, X("rho"))), Trace(X("rho"))))));
        Formula groundProjector = At(Qualified("Matrix", "vecMulVec"), X("g"), StarOf(X("g")));
        Formula memoryTrace = At(Named("partialTraceRight"), X("sigma"));
        Formula energy = RealPart(Trace(Multiply(X("ham"), At(local, memoryTrace))));
        Formula bound = Subtract(Multiply(D(2), new Formula.Power(
            Parenthesized(Subtract(D(1), Multiply(D(2), Omega))), D(2))), D(1));
        Formula conditions = Conjunction(
            Psd(X("sigma")), Equal(Trace(X("sigma")), D(1)), channels,
            At(Qualified("Matrix", "IsHermitian"), X("ham")),
            Equal(At(Named("dotProduct"), StarOf(X("g")), X("g")), D(1)),
            Equal(At(Qualified("Matrix", "mulVec"), X("ham"), X("g")), D(0)),
            Psd(Subtract(X("ham"), Parenthesized(Subtract(D(1), groundProjector)))),
            All("b", FinOf(D(2)), Psd(At(X("povm"), X("b")))),
            Equal(Add(At(X("povm"), D(0)), At(X("povm"), D(1))), D(1)),
            All("x", FinOf(D(2)), LessEqual(energy, Omega)),
            Equal(Probability(D(0), D(0)), D(1)),
            Less(Subtract(Probability(D(0), D(1)), Probability(D(1), D(1))), bound));
        Formula objects = Some("dp", Naturals, Some("ds", Naturals, Some("dm", Naturals,
            Some("sigma", MatrixOf(Product(dp, dm)),
            Some("lam", Arrow(FinOf(D(2)), MatrixMapOf(dp, ds)),
            Some("ham", MatrixOf(ds), Some("g", Arrow(ds, Complexes),
            Some("povm", Arrow(FinOf(D(2)), MatrixOf(Product(ds, dm))), conditions))))))));
        return All(Omega, Reals, Implies(Less(D(0), Omega),
            Implies(Less(Omega, new Formula.Fraction(D(1), D(2))), objects)));
    }
}
