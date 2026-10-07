using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class InertGroupBlockConjugacyDocument : IScribeDocumentDefinition
{
    private const string StationaryPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable StationaryB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula StationaryAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula StationaryExists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula StationaryAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula StationaryImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula StationaryIff(Formula a, Formula b) => StationaryAnd(StationaryImplies(a, b), StationaryImplies(b, a));
    private static Formula StationaryId(string name) => F.Id(name);
    private static Formula StationaryEnd => Call("ModuleEnd", StationaryId("R"), StationaryId("M"));
    private static Formula StationaryIdentityFamily => StationaryAll(
        Equal(Call("induced", StationaryId("T"), Call("apply", StationaryId("P"), StationaryId("g")), Call("apply", StationaryId("commutes"), StationaryId("g"))),
            Call("linearIdentity", Call("StationaryModule", StationaryId("T")))), StationaryB("g", StationaryId("Gamma")));
    private static Formula StationaryCommonStage => StationaryExists("N", StationaryId("Nat"), StationaryAll(
        Equal(Call("compose", Call("power", StationaryId("T"), StationaryId("N")), Call("apply", StationaryId("P"), StationaryId("g"))),
            Call("power", StationaryId("T"), StationaryId("N"))), StationaryB("g", StationaryId("Gamma"))));
    private static Formula StationaryClaim => StationaryAll(StationaryIff(StationaryIdentityFamily, StationaryCommonStage),
        StationaryB("R", StationaryId("Type")), StationaryB("commRingR", Call("CommRing", StationaryId("R"))),
        StationaryB("M", StationaryId("Type")), StationaryB("addGroupM", Call("AddCommGroup", StationaryId("M"))),
        StationaryB("moduleM", Call("Module", StationaryId("R"), StationaryId("M"))),
        StationaryB("I", StationaryId("Type")), StationaryB("finiteI", Call("Fintype", StationaryId("I"))),
        StationaryB("Gamma", StationaryId("Type")), StationaryB("finiteGamma", Call("Fintype", StationaryId("Gamma"))),
        StationaryB("basis", Call("Basis", StationaryId("I"), StationaryId("R"), StationaryId("M"))),
        StationaryB("T", StationaryEnd), StationaryB("P", Call("Function", StationaryId("Gamma"), StationaryEnd)),
        StationaryB("commutes", StationaryAll(Call("Commute", Call("apply", StationaryId("P"), StationaryId("g")), StationaryId("T")), StationaryB("g", StationaryId("Gamma")))));

    private const string NaturalPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable NaturalB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula NaturalAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula NaturalAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula NaturalImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula NaturalIff(Formula a, Formula b) => NaturalAnd(NaturalImplies(a, b), NaturalImplies(b, a));
    private static Formula NaturalLe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula NaturalId(string name) => F.Id(name);
    private static Formula.BoundVariable[] NaturalGroupData => [
        NaturalB("H", NaturalId("Type")), NaturalB("groupH", Call("Group", NaturalId("H"))),
        NaturalB("finiteH", Call("Fintype", NaturalId("H"))), NaturalB("n", NaturalId("Nat"))];
    private static Formula NaturalGroupMat => Call("GroupMat", NaturalId("H"), NaturalId("n"), NaturalId("n"));
    private static Formula NaturalTau(string name) => Call("tau", NaturalId(name));
    private static Formula NaturalUniformPower(string name) => Call("UniformMatrix", Call("matrixPower", NaturalId(name), NaturalId("k")));
    private static Formula NaturalTauClaim => NaturalAll(NaturalIff(NaturalLe(NaturalTau("A"), Call("finiteWithTop", NaturalId("k"))),
        NaturalAnd(Call("NatPositive", NaturalId("k")), NaturalUniformPower("A"))),
        [.. NaturalGroupData, NaturalB("A", NaturalGroupMat), NaturalB("k", NaturalId("Nat"))]);
    private static Formula NaturalOneClaim => NaturalAll(NaturalIff(Equal(NaturalTau("A"), Call("finiteWithTop", D(1))),
        Call("UniformMatrix", NaturalId("A"))), [.. NaturalGroupData, NaturalB("A", NaturalGroupMat)]);
    private static Formula NaturalPowerClaim => NaturalAll(NaturalAnd(Call("NatPositive", NaturalId("k")),
        Equal(Call("matrixPower", NaturalId("A"), NaturalId("k")), Call("matrixPower", NaturalId("B"), NaturalId("k")))),
        [.. NaturalGroupData, NaturalB("A", NaturalGroupMat), NaturalB("B", NaturalGroupMat),
         NaturalB("sameAugmentation", Equal(Call("matrixAugmentation", NaturalId("A")), Call("matrixAugmentation", NaturalId("B")))),
         NaturalB("k", NaturalId("Nat")), NaturalB("threshold", NaturalLe(Call("max", NaturalTau("A"), NaturalTau("B")), Call("finiteWithTop", NaturalId("k"))))]);

    private const string RationalPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable RationalB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula RationalAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula RationalAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula RationalImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula RationalIff(Formula a, Formula b) => RationalAnd(RationalImplies(a, b), RationalImplies(b, a));
    private static Formula RationalId(string name) => F.Id(name);
    private static Formula.BoundVariable[] RationalGroupData => [
        RationalB("H", RationalId("Type")), RationalB("groupH", Call("Group", RationalId("H"))), RationalB("finiteH", Call("Fintype", RationalId("H")))];
    private static Formula RationalAlgebraH => Call("MonoidAlgebra", RationalId("Rat"), RationalId("H"));
    private static Formula RationalTailClaim => RationalAll(RationalIff(Call("UniformRational", RationalId("x")),
        Equal(Call("second", Call("apply", RationalId("phi"), RationalId("x"))), D(0))),
        [.. RationalGroupData, RationalB("S", RationalId("Type")), RationalB("ringS", Call("Ring", RationalId("S"))),
         RationalB("algebraS", Call("Algebra", RationalId("Rat"), RationalId("S"))),
         RationalB("phi", Call("AlgEquiv", RationalId("Rat"), RationalAlgebraH, Call("Product", RationalId("Rat"), RationalId("S")))),
         RationalB("augmentationFirst", RationalAll(Equal(Call("first", Call("apply", RationalId("phi"), RationalId("z"))),
             Call("augmentation", RationalId("z"))), RationalB("z", RationalAlgebraH))), RationalB("x", RationalAlgebraH)]);
    private static Formula RationalExistenceClaim => RationalAll(Call("Nonempty", Call("RationalDecomposition", RationalId("H"))),
        [.. RationalGroupData, RationalB("nontrivialH", Call("Nontrivial", RationalId("H")))]);
    private static Formula RationalUniformClaim => RationalAll(Equal(RationalId("x"),
        Call("scalarMultiply", Call("augmentation", RationalId("x")), Call("average", RationalId("H")))),
        [.. RationalGroupData, RationalB("x", RationalAlgebraH), RationalB("uniform", Call("UniformRational", RationalId("x")))]);

    private const string CutoffPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable CutoffB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula CutoffAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula CutoffAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CutoffImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula CutoffIff(Formula a, Formula b) => CutoffAnd(CutoffImplies(a, b), CutoffImplies(b, a));
    private static Formula CutoffLe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CutoffId(string name) => F.Id(name);
    private static Formula.BoundVariable[] CutoffGroupData => [
        CutoffB("H", CutoffId("Type")), CutoffB("groupH", Call("Group", CutoffId("H"))),
        CutoffB("finiteH", Call("Fintype", CutoffId("H"))), CutoffB("n", CutoffId("Nat"))];
    private static Formula CutoffGroupMat => Call("GroupMat", CutoffId("H"), CutoffId("n"), CutoffId("n"));
    private static Formula CutoffDecomposition => Call("RationalDecomposition", CutoffId("H"));
    private static Formula CutoffBlocksClaim => CutoffAll(CutoffIff(Call("UniformMatrix", CutoffId("C")),
        CutoffAll(Equal(Call("block", CutoffId("W"), CutoffId("l"), CutoffId("C")), D(0)),
            CutoffB("l", Call("Fin", Call("count", CutoffId("W")))))),
        [.. CutoffGroupData, CutoffB("W", CutoffDecomposition), CutoffB("C", CutoffGroupMat)]);
    private static Formula CutoffCutoffClaim => CutoffAll(CutoffLe(Call("tau", CutoffId("A")),
        Call("finiteWithTop", Call("multiply", CutoffId("n"), Call("bH", CutoffId("W"))))),
        [.. CutoffGroupData, CutoffB("W", CutoffDecomposition), CutoffB("positiveN", Call("NatPositive", CutoffId("n"))),
         CutoffB("A", CutoffGroupMat), CutoffB("uniformizes", Call("Uniformizes", CutoffId("A")))]);
    private static Formula CutoffRationalClaim => CutoffAll(Equal(Call("rationalEntry", CutoffId("C"), CutoffId("i"), CutoffId("j")),
        Call("scalarMultiply", Call("castRat", Call("augmentationEntry", CutoffId("C"), CutoffId("i"), CutoffId("j"))),
            Call("average", CutoffId("H")))),
        [.. CutoffGroupData, CutoffB("C", CutoffGroupMat), CutoffB("uniform", Call("UniformMatrix", CutoffId("C"))),
         CutoffB("i", Call("Fin", CutoffId("n"))), CutoffB("j", Call("Fin", CutoffId("n")))]);

    private const string ExpansionPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable ExpansionB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula ExpansionAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula ExpansionAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ExpansionImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula ExpansionIff(Formula a, Formula b) => ExpansionAnd(ExpansionImplies(a, b), ExpansionImplies(b, a));
    private static Formula ExpansionId(string name) => F.Id(name);
    private static Formula.BoundVariable[] ExpansionGroupData => [
        ExpansionB("H", ExpansionId("Type")), ExpansionB("groupH", Call("Group", ExpansionId("H"))),
        ExpansionB("finiteH", Call("Fintype", ExpansionId("H"))), ExpansionB("n", ExpansionId("Nat"))];
    private static Formula ExpansionGroupMat => Call("GroupMat", ExpansionId("H"), ExpansionId("n"), ExpansionId("n"));
    private static Formula ExpansionAdjacencyClaim => ExpansionAll(Equal(
        Call("coefficient", Call("vertexCoordinate", Call("apply", Call("transition", ExpansionId("A")),
            Call("vertex", ExpansionId("i"), ExpansionId("h"))), ExpansionId("j")), ExpansionId("t")),
        Call("castInt", Call("coefficient", Call("entry", ExpansionId("A"), ExpansionId("i"), ExpansionId("j")),
            Call("multiply", Call("inverse", ExpansionId("h")), ExpansionId("t"))))),
        [.. ExpansionGroupData, ExpansionB("A", ExpansionGroupMat), ExpansionB("i", Call("Fin", ExpansionId("n"))), ExpansionB("j", Call("Fin", ExpansionId("n"))),
         ExpansionB("h", ExpansionId("H")), ExpansionB("t", ExpansionId("H"))]);
    private static Formula ExpansionInertClaim => ExpansionAll(ExpansionIff(Call("Inert", ExpansionId("A")), Call("Uniformizes", ExpansionId("A"))),
        [.. ExpansionGroupData, ExpansionB("A", ExpansionGroupMat)]);

    private const string InertPrefix = "D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.";
    private static Formula.BoundVariable InertB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula InertAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula InertExists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula InertAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula InertImplies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula InertLe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula InertId(string name) => F.Id(name);
    private static Formula InertApply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula InertGroupMat => Call("GroupMat", InertId("H"), InertId("n"), InertId("n"));
    private static Formula InertGraph(string name) => Call("expandedGraph", InertId(name));
    private static Formula InertHistoryA => Call("History", InertGraph("A"));
    private static Formula InertTau(string name) => Call("tau", InertId(name));
    private static Formula InertMaxTau => Call("max", InertTau("A"), InertTau("B"));
    private static Formula InertPower(string name) => Call("matrixPower", InertId(name), InertId("k"));
    private static Formula InertConstructedMap => Call("equalPowerHomeomorph", InertId("A"), InertId("B"), InertId("hk"), InertId("hpower"));
    private static Formula InertCounts => Call("equalPowerFiberCounts", InertId("A"), InertId("B"), InertId("hk"), InertId("hpower"));
    private static Formula InertRationalPower(string name) => InertAll(Equal(
        Call("rationalEntry", InertPower(name), InertId("i"), InertId("j")),
        Call("scalarMultiply", Call("castRat", Call("entry",
            Call("matrixPower", Call("matrixAugmentation", InertId("A")), InertId("k")), InertId("i"), InertId("j"))),
            Call("average", InertId("H")))), InertB("i", Call("Fin", InertId("n"))), InertB("j", Call("Fin", InertId("n"))));
    private static Formula InertOperational => InertAll(Equal(
        Call("original181History", InertId("A"), InertId("B"), InertId("hk"), InertCounts, InertId("x")),
        InertApply(InertConstructedMap, InertId("x"))), InertB("x", InertHistoryA));
    private static Formula InertEquivariant => InertAll(Equal(
        InertApply(InertConstructedMap, Call("groupHistory", InertId("A"), InertId("a"), InertId("x"))),
        Call("groupHistory", InertId("B"), InertId("a"), InertApply(InertConstructedMap, InertId("x")))),
        InertB("a", InertId("H")), InertB("x", InertHistoryA));
    private static Formula InertBlockTime => InertAll(Equal(
        InertApply(InertConstructedMap, Call("iterate", Call("shift", InertGraph("A")), InertId("k"), InertId("x"))),
        Call("iterate", Call("shift", InertGraph("B")), InertId("k"), InertApply(InertConstructedMap, InertId("x")))), InertB("x", InertHistoryA));
    private static Formula InertUnitTime => InertAll(Equal(
        InertApply(InertConstructedMap, Call("shift", InertGraph("A"), InertId("x"))),
        Call("shift", InertGraph("B"), InertApply(InertConstructedMap, InertId("x")))), InertB("x", InertHistoryA));
    private static Formula InertAtExponent => InertExists("hk", Call("NatPositive", InertId("k")),
        InertExists("hpower", Equal(InertPower("A"), InertPower("B")),
            InertAnd(InertRationalPower("A"), InertAnd(InertRationalPower("B"),
                InertAnd(InertOperational, InertAnd(InertEquivariant, InertAnd(InertBlockTime, InertImplies(InertUnitTime, Equal(InertId("A"), InertId("B"))))))))));
    private static Formula InertTrivialBoundary => InertImplies(Call("Subsingleton", InertId("H")),
        InertAnd(Equal(InertTau("A"), Call("finiteWithTop", D(1))),
            InertAnd(Equal(InertTau("B"), Call("finiteWithTop", D(1))), Equal(InertId("A"), InertId("B")))));
    private static Formula InertRationalCutoff => InertAll(InertLe(InertMaxTau,
        Call("finiteWithTop", Call("multiply", InertId("n"), Call("bH", InertId("W"))))),
        InertB("W", Call("RationalDecomposition", InertId("H"))), InertB("positiveN", Call("NatPositive", InertId("n"))));
    private static Formula InertEveryExponent => InertAll(InertAtExponent,
        InertB("k", InertId("Nat")), InertB("threshold", InertLe(InertMaxTau, Call("finiteWithTop", InertId("k")))));
    private static Formula InertChosenCutoff =>
        Call("finiteWithTop", Call("multiply", InertId("n"), Call("bH", InertId("W"))));
    private static Formula InertAfterChosenCutoff => InertAll(InertAtExponent,
        InertB("k", InertId("Nat")),
        InertB("threshold", InertLe(InertChosenCutoff, Call("finiteWithTop", InertId("k")))));
    private static Formula InertActualDecomposition => InertImplies(Call("Nontrivial", InertId("H")),
        InertImplies(Call("NatPositive", InertId("n")),
            InertExists("W", Call("RationalDecomposition", InertId("H")),
                InertAnd(InertLe(InertMaxTau, InertChosenCutoff), InertAfterChosenCutoff))));
    private static Formula InertClaim => InertAll(InertAnd(InertAnd(InertTrivialBoundary, InertAnd(InertRationalCutoff, InertEveryExponent)), InertActualDecomposition),
        InertB("H", InertId("Type")), InertB("groupH", Call("Group", InertId("H"))),
        InertB("finiteH", Call("Fintype", InertId("H"))), InertB("n", InertId("Nat")),
        InertB("topologyH", Call("TopologicalSpace", InertId("H"))), InertB("discreteH", Call("DiscreteTopology", InertId("H"))),
        InertB("A", InertGroupMat), InertB("B", InertGroupMat),
        InertB("essentialA", Call("Essential", Call("baseGraph", InertId("A")))),
        InertB("essentialB", Call("Essential", Call("baseGraph", InertId("B")))),
        InertB("inertA", Call("Inert", InertId("A"))), InertB("inertB", Call("Inert", InertId("B"))),
        InertB("sameAugmentation", Equal(Call("matrixAugmentation", InertId("A")), Call("matrixAugmentation", InertId("B")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual stationary actions and rational splitting give every original positive-threshold block construction.",
        H("Inert group block conjugacy"), Blocks(
            Describe.Lean(DescribeId.Create("finite-family-stationary-identity"),
                DeclarationHandle.Create(StationaryPrefix + "finite_family_inert_iff_eventual"), H("One common annihilation stage"),
                StatementSource.FromAuthor(Disp(StationaryClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("StationaryModule(T) is the actual module direct limit with transition from stage i to stage j equal to T raised to j minus i. The commuting endomorphism P(g) induces the displayed map on this direct limit. Powers of endomorphisms use composition, so the finite-stage equation is T^N composed with P(g) equals T^N.")),
                    Paragraph(Text("Equality of two stage-zero classes is witnessed at a later stage by direct-limit exactness. There are finitely many basis vectors and finitely many family members; taking finite maxima gives one N for all of them. Conversely the same finite-stage equation holds after every starting stage, so it forces identity on the entire colimit. The exponent N may be zero, the basis may be empty, and the family need not be a group action."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-tau-exact-threshold"),
                DeclarationHandle.Create(NaturalPrefix + "tau_le_iff_uniform_power"), H("Every admissible exponent"),
                StatementSource.FromAuthor(Disp(NaturalTauClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("GroupMat(H,n,n) is the matrix semiring over the natural group algebra. UniformMatrix means every actual group coefficient in each entry equals its coefficient at the identity, including zero coefficients. The value tau lies in the natural numbers with a top element: it is the least positive uniform exponent when one exists and infinity otherwise. Ordered convolution preserves uniformity under right multiplication, without assuming the finite group H is commutative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tau-one-uniform-boundaries"),
                DeclarationHandle.Create(NaturalPrefix + "tau_eq_one_iff_uniform"), H("The positive convention includes zero"),
                StatementSource.FromAuthor(Disp(NaturalOneClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence includes the zero matrix, whose least positive exponent is one even though its zeroth power behaves differently. If H is trivial, every entry is uniform and every matrix has tau one. It also includes n=0; no positivity of the matrix order is needed for the natural threshold theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("natural-powers-at-max-tau"),
                DeclarationHandle.Create(NaturalPrefix + "equal_power_of_tau_le"), H("Equal augmentation gives equal natural powers"),
                StatementSource.FromAuthor(Disp(NaturalPowerClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Augmentation sums the actual natural coefficients entry by entry and is a ring homomorphism. At every k at least both tau values, both powers are uniform. A uniform natural entry is determined by its augmentation because its coefficient sum is |H| times any coefficient and |H| is positive. Thus A^k=B^k in the original natural group-matrix semiring. Positivity of k is a conclusion; k=1 is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-tail-kernel"),
                DeclarationHandle.Create(RationalPrefix + "uniform_iff_tail_zero"), H("The exact kernel of the nontrivial tail"),
                StatementSource.FromAuthor(Disp(RationalTailClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UniformRational means equality of every coefficient with the identity coefficient. Augmentation is their rational sum. The normalized element average(H), denoted e_H, has every coefficient 1/|H|. The theorem applies to any actual rational algebra equivalence phi whose first coordinate is literally augmentation; S may be noncommutative. A uniform element satisfies x*y=augmentation(y) times x. Conversely, vanishing tail makes every left group translation fix x and hence makes every coefficient equal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmentation-first-rational-decomposition"),
                DeclarationHandle.Create(RationalPrefix + "nonempty_decomposition"), H("All nontrivial rational simple factors"),
                StatementSource.FromAuthor(Disp(RationalExistenceClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RationalDecomposition(H) consists of a positive count m, a division algebra D_l over the rationals of finite rational dimension for each l in Fin(m), positive natural matrix orders r_l, and an actual rational algebra equivalence Q[H] with Q times the product of Mat(r_l,D_l). Its first coordinate equals augmentation on every element. No complex splitting or change of coefficient field occurs.")),
                    Paragraph(Text("Uniform elements form a two-sided ideal J. The map x to (augmentation(x),[x]) is bijective: its kernel is zero because a uniform augmentation-zero element is zero, and a preimage of (a,[x]) is x+(a-augmentation(x))*e_H. For nontrivial H the quotient Q[H]/J is nontrivial. Maschke supplies semisimplicity and the finite rational Wedderburn theorem supplies the division-ring factors of this quotient. The quotient's nontriviality makes the factor count positive; no empty maximum is assigned to a trivial group."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-normalized-rational-expression"),
                DeclarationHandle.Create(RationalPrefix + "uniform_eq_augmentation_smul_average"), H("The exact normalized expression"),
                StatementSource.FromAuthor(Disp(RationalUniformClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every uniform rational element is its actual augmentation times e_H. This includes zero and preserves the factor 1/|H| exactly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-natural-matrix-block-kernel"),
                DeclarationHandle.Create(CutoffPrefix + "uniform_iff_blocks_zero"), H("Actual uniformity and faithful blocks"),
                StatementSource.FromAuthor(Disp(CutoffBlocksClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W is an actual augmentation-first rational decomposition with positive factor count, positive matrix orders r_l and finite rational division algebras D_l. The map block(W,l,C) casts natural coefficients to rational coefficients, applies the l-th tail factor entrywise, then flattens Mat(n,Mat(r_l,D_l)) to Mat(Fin(n) times Fin(r_l),D_l). Faithfulness and augmentation-firstness identify its simultaneous zero kernel with uniform coefficients. This is a theorem about every C, not an assumed bridge for selected powers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("least-positive-rational-cutoff"),
                DeclarationHandle.Create(CutoffPrefix + "tau_le_cutoff"), H("The exact bound n*b_H"),
                StatementSource.FromAuthor(Disp(CutoffCutoffClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The natural number bH(W) is the maximum of W's original nontrivial rational matrix orders r_l. A positive uniform power makes every tail block nilpotent. Right multiplication on row vectors is linear over the same division ring and reverses products, but preserves powers of one matrix. Kernel stabilization therefore kills an n*r_l dimensional block by exponent n*r_l, and hence all blocks vanish by n*bH(W).")),
                    Paragraph(Text("The dimension is measured over D_l, not over the rationals; there is no factor dim_Q(D_l). The hypotheses n>0, positive factor count and positive r_l ensure that n*bH(W) is a positive exponent, as required by the least-positive convention. The trivial group uses the separate tau=1 boundary and has no artificial b_H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("natural-uniform-rational-formula"),
                DeclarationHandle.Create(CutoffPrefix + "uniform_rational_expression"), H("Rational expression of a natural uniform matrix"),
                StatementSource.FromAuthor(Disp(CutoffRationalClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rationalEntry(C,i,j) is the natural entry C[i,j] with its coefficients cast to the rationals; augmentationEntry is the natural augmentation entry. The equality is entrywise equality in Q[H]. It divides only after casting to the rationals and does not assert divisibility by introducing an operation in the natural semiring."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-free-expansion-adjacency"),
                DeclarationHandle.Create(ExpansionPrefix + "actual_expansion_adjacency"), H("Ordered vertex coordinates"),
                StatementSource.FromAuthor(Disp(ExpansionAdjacencyClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("VertexModule is Fin(n) to Z[H], the free abelian group on vertices (i,h). The vector vertex(i,h) has coefficient one at that vertex and zero elsewhere. The transition sends a row vector v to v times the coefficientwise integer cast of A. The displayed coefficient is exactly the number of actual expanded edges from (i,h) to (j,t): an edge labelled s ends at h*s, so s=h inverse times t. The order is retained for noncommutative H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-inertness-positive-uniformization"),
                DeclarationHandle.Create(ExpansionPrefix + "inert_iff_uniformizes"), H("Identity on the actual stationary group"),
                StatementSource.FromAuthor(Disp(ExpansionInertClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("DimensionGroup(A) is the actual stationary module colimit of this integer transition. The original left H-action sends each vertex (i,h) to (i,g*h), commutes with adjacency, and therefore induces groupAction(A,g) on that colimit. Inert(A) means groupAction(A,g) equals the identity for every g; uniformization is not part of this definition. Uniformizes(A) means that some positive natural exponent has all actual group coefficients constant in each matrix entry.")),
                    Paragraph(Text("The finite vertex basis and finite group give a common stage N at which T_A^N composed with every left translation equals T_A^N. Reading basis coefficients equates every coefficient of A^N; conversely uniform coefficients imply those stage equations on the basis. Advancing from N to N+1 supplies a positive exponent even when the common stage was zero. Inertness is identity on the underlying stationary group; the argument does not require a separately constructed ordered-group API or an order-unit normalization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original18-1-inert-full-attachment"),
                DeclarationHandle.Create(InertPrefix + "original18_1"), H("The full threshold and unchanged construction"),
                StatementSource.FromAuthor(Disp(InertClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A and B are natural group-ring matrices with the same actual augmentation matrix. Their finite base graphs are essential, and their original left H-actions are inert on the stationary dimension groups of the actual integer free-expansion adjacencies. NatPositive means strictly positive. The displayed equalPowerFiberCounts denotes the existing fiber_counts_of_equal_power proof on the same A, B, hk and hpower. Tau is the least positive uniform exponent, or infinity if no such exponent exists. The displayed existential proofs hk and hpower express conclusions 0<k and A^k=B^k; neither is an additional premise.")),
                    Paragraph(Text("The final conjunct supplies an actual single decomposition W when H is nontrivial and n is positive. Its own original block orders give the displayed cutoff, and this same W controls the constructed map for every k at least that cutoff. No decomposition or cutoff is an extra premise. The preceding clauses still cover every supplied W and every k at least max tau, including smaller admissible exponents. For nontrivial H, an augmentation-first RationalDecomposition is supplied by the rational splitting theorem. The cutoff clause holds for every such decomposition W and every positive n. It retains W's original nontrivial rational block orders r_l, with bH(W)=max_l r_l, giving max(tau(A),tau(B)) at most n*bH(W). Therefore every k at least n*bH(W) satisfies the final clause, while all smaller k at least the original max-tau threshold remain included. For trivial H both tau values are one and equal augmentation already gives A=B. Zero matrices have tau one by the positive convention; no empty b_H is assigned.")),
                    Paragraph(Text("The rational equations are equalities in Q[H] at each entry: both A^k and B^k equal the corresponding entry of the k-th power of their common augmentation matrix times e_H, whose actual coefficients are 1/|H|. The equality A^k=B^k itself is in the natural group-matrix semiring. No commutativity of H or replacement by complex irreducible degrees is used.")),
                    Paragraph(Text("For each admissible k, the exact equalPowerHomeomorph uses the existing ordered-label fiber bijections and the same fixed nonoverlapping integer blocks [jk,(j+1)k-1]. Operational equality identifies original181History with this homeomorphism; the next equations give the original left H-equivariance and the k-step shift law for this same map. Positive and negative positions use the same quotient-and-remainder construction, and k=1 is included. Different k may give different maps.")),
                    Paragraph(Text("If this exact fixed-block map also commutes with the original one-step shift, essentiality and fixed-block rigidity force A=B. The conclusion does not forbid other overlapping codes, other state presentations or other original-time conjugacies. No unit-time conjugacy is claimed from inertness alone."))), DescribeRole.Theorem))));
}
