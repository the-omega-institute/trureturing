using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class InertGroupBlockConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula GroupMat => Call("GroupMat", Id("H"), Id("n"), Id("n"));
    private static Formula Graph(string name) => Call("expandedGraph", Id(name));
    private static Formula HistoryA => Call("History", Graph("A"));
    private static Formula Tau(string name) => Call("tau", Id(name));
    private static Formula MaxTau => Call("max", Tau("A"), Tau("B"));
    private static Formula Power(string name) => Call("matrixPower", Id(name), Id("k"));
    private static Formula ConstructedMap => Call("equalPowerHomeomorph", Id("A"), Id("B"), Id("hk"), Id("hpower"));
    private static Formula Counts => Call("equalPowerFiberCounts", Id("A"), Id("B"), Id("hk"), Id("hpower"));
    private static Formula RationalPower(string name) => All(Equal(
        Call("rationalEntry", Power(name), Id("i"), Id("j")),
        Call("scalarMultiply", Call("castRat", Call("entry",
            Call("matrixPower", Call("matrixAugmentation", Id("A")), Id("k")), Id("i"), Id("j"))),
            Call("average", Id("H")))), B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n"))));
    private static Formula Operational => All(Equal(
        Call("original181History", Id("A"), Id("B"), Id("hk"), Counts, Id("x")),
        Apply(ConstructedMap, Id("x"))), B("x", HistoryA));
    private static Formula Equivariant => All(Equal(
        Apply(ConstructedMap, Call("groupHistory", Id("A"), Id("a"), Id("x"))),
        Call("groupHistory", Id("B"), Id("a"), Apply(ConstructedMap, Id("x")))),
        B("a", Id("H")), B("x", HistoryA));
    private static Formula BlockTime => All(Equal(
        Apply(ConstructedMap, Call("iterate", Call("shift", Graph("A")), Id("k"), Id("x"))),
        Call("iterate", Call("shift", Graph("B")), Id("k"), Apply(ConstructedMap, Id("x")))), B("x", HistoryA));
    private static Formula UnitTime => All(Equal(
        Apply(ConstructedMap, Call("shift", Graph("A"), Id("x"))),
        Call("shift", Graph("B"), Apply(ConstructedMap, Id("x")))), B("x", HistoryA));
    private static Formula AtExponent => Exists("hk", Call("NatPositive", Id("k")),
        Exists("hpower", Equal(Power("A"), Power("B")),
            And(RationalPower("A"), And(RationalPower("B"),
                And(Operational, And(Equivariant, And(BlockTime, Implies(UnitTime, Equal(Id("A"), Id("B"))))))))));
    private static Formula TrivialBoundary => Implies(Call("Subsingleton", Id("H")),
        And(Equal(Tau("A"), Call("finiteWithTop", D(1))),
            And(Equal(Tau("B"), Call("finiteWithTop", D(1))), Equal(Id("A"), Id("B")))));
    private static Formula RationalCutoff => All(Le(MaxTau,
        Call("finiteWithTop", Call("multiply", Id("n"), Call("bH", Id("W"))))),
        B("W", Call("RationalDecomposition", Id("H"))), B("positiveN", Call("NatPositive", Id("n"))));
    private static Formula EveryExponent => All(AtExponent,
        B("k", Id("Nat")), B("threshold", Le(MaxTau, Call("finiteWithTop", Id("k")))));
    private static Formula Claim => All(And(TrivialBoundary, And(RationalCutoff, EveryExponent)),
        B("H", Id("Type")), B("groupH", Call("Group", Id("H"))),
        B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat")),
        B("topologyH", Call("TopologicalSpace", Id("H"))), B("discreteH", Call("DiscreteTopology", Id("H"))),
        B("A", GroupMat), B("B", GroupMat),
        B("essentialA", Call("Essential", Call("baseGraph", Id("A")))),
        B("essentialB", Call("Essential", Call("baseGraph", Id("B")))),
        B("inertA", Call("Inert", Id("A"))), B("inertB", Call("Inert", Id("B"))),
        B("sameAugmentation", Equal(Call("matrixAugmentation", Id("A")), Call("matrixAugmentation", Id("B")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual dimension-group inertness gives the original positive thresholds and the exact fixed-block conjugacy at every admissible exponent.",
        H("Original18.1: inert group block conjugacy"), Blocks(
            Describe.Lean(DescribeId.Create("original18-1-inert-full-attachment"),
                DeclarationHandle.Create(Prefix + "original18_1"), H("The full threshold and unchanged construction"),
                StatementSource.FromAuthor(Disp(Claim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A and B are natural group-ring matrices with the same actual augmentation matrix. Their finite base graphs are essential, and their original left H-actions are inert on the stationary dimension groups of the actual integer free-expansion adjacencies. NatPositive means strictly positive. The displayed equalPowerFiberCounts denotes the existing fiber_counts_of_equal_power proof on the same A, B, hk and hpower. Tau is the least positive uniform exponent, or infinity if no such exponent exists. The displayed existential proofs hk and hpower express conclusions 0<k and A^k=B^k; neither is an additional premise.")),
                    Paragraph(Text("For nontrivial H, an augmentation-first RationalDecomposition is supplied by the rational splitting theorem. The cutoff clause holds for every such decomposition W and every positive n. It retains W's original nontrivial rational block orders r_l, with bH(W)=max_l r_l, giving max(tau(A),tau(B)) at most n*bH(W). Therefore every k at least n*bH(W) satisfies the final clause, while all smaller k at least the original max-tau threshold remain included. For trivial H both tau values are one and equal augmentation already gives A=B. Zero matrices have tau one by the positive convention; no empty b_H is assigned.")),
                    Paragraph(Text("The rational equations are equalities in Q[H] at each entry: both A^k and B^k equal the corresponding entry of the k-th power of their common augmentation matrix times e_H, whose actual coefficients are 1/|H|. The equality A^k=B^k itself is in the natural group-matrix semiring. No commutativity of H or replacement by complex irreducible degrees is used.")),
                    Paragraph(Text("For each admissible k, the exact equalPowerHomeomorph uses the existing ordered-label fiber bijections and the same fixed nonoverlapping integer blocks [jk,(j+1)k-1]. Operational equality identifies original181History with this homeomorphism; the next equations give the original left H-equivariance and the k-step shift law for this same map. Positive and negative positions use the same quotient-and-remainder construction, and k=1 is included. Different k may give different maps.")),
                    Paragraph(Text("If this exact fixed-block map also commutes with the original one-step shift, essentiality and fixed-block rigidity force A=B. The conclusion does not forbid other overlapping codes, other state presentations or other original-time conjugacies. No unit-time conjugacy is claimed from inertness alone."))), DescribeRole.Theorem))));
}
