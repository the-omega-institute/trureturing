using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class HeisenbergCentralRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual complex compact smooth Heisenberg graph has a single-valued closed gradient and a central derivative with zero kernel on the whole space.",
        H("Central Rigidity of the Whole Heisenberg Graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("heisenberg-central-rigidity"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/HeisenbergCentralRigidity.central_rigidity"),
            H("Joint closure, complex weak central differentiation and whole-line rigidity"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The coordinate space is EuclideanSpace Real (Fin 3), identified with triples (x,y,z). Its measure is raw Lebesgue volume, and State is the complex L2 space for this measure. The frame consists, in order, of U = partial_x - (y/2) partial_z, V = partial_y + (x/2) partial_z, and Z = partial_z. The derivatives are real directional derivatives of complex functions.")),
                Paragraph(Text("In the formula, Space, State, Components and Ambient denote exactly EuclideanSpace Real (Fin 3), Lp Complex 2 volume, Fin 3 to State, and State times Components. The indices 0, 1 and 2 select U, V and Z. fst and snd are the product projections; rep(v) is the function coercion (v : Space to Complex) of an L2 class. axis(i) is EuclideanSpace.single i 1. The expression fderiv(Real,f,x,b) means the real Frechet derivative fderiv Real f x applied to b, and conj is complex conjugation.")),
                Paragraph(Text("compactCore consists of precisely the compactly supported complex Schwartz functions. Every complex smooth compactly supported function gives such a Schwartz function through HasCompactSupport.toSchwartzMap, with the same values and derivatives. coreJet records its L2 state together with all three L2 field derivatives. jointGraph is the topological closure of the range of this one linear map in the product of the state space and the three component spaces. Thus one approximating function supplies all four coordinates simultaneously. No component is discarded and no replacement by isotropic Euclidean H1 is made.")),
                Paragraph(Text("More explicitly, field(i) acts on a Schwartz function by fderiv Real in the direction frame(i,x). For phi in compactCore, coreJet(phi) has state phi.toLp 2 volume and component i equal to (field i phi).toLp 2 volume, using the underlying Schwartz function. coreOperator is (LinearMap.range coreJet).toLinearPMap, a complex partial linear map from State to Components; closedOperator is coreOperator.closure. domain and graph are the corresponding LinearPMap projections, and jointGraph is (LinearMap.range coreJet).topologicalClosure. Dense uses the underlying subset of State; IsClosable and IsClosed are the LinearPMap predicates, and graph membership uses the underlying subset of Ambient.")),
                Paragraph(Text("The symbol smoothOrder is WithTop.some ENat.top, the coercion of (top : ENat) used in ContDiff Real (top : ENat), so the tests are smooth rather than analytic. The bound s is the common Nat-to-compactCore sequence, and e is an arbitrary Space-to-Complex test. Each indexed family (a(x)) with x in a displayed type denotes the function x mapping to a(x). Tendsto uses atTop on Nat and the norm-neighbourhood filter nhds of its displayed L2 limit. In the integrals x ranges over Space and d volume is raw Lebesgue measure. EventuallyEq(ae(volume),a,b) means a = almost everywhere b for that measure, including the representative equalities in the last conjunct. The two zero symbols in the central equivalence are the zero of State.")),
                Paragraph(Text("The compact-core state projection is dense. Its joint gradient coreOperator is closable, and the graph of its Mathlib partial-linear-map closure closedOperator equals jointGraph. Two members of this graph with the same state have identical triples of components. The existence of the closure constructor alone is insufficient: the proof establishes the absence of nonzero vertical graph vectors, using the injective continuous embedding of L2 into tempered distributions and the three distributional field equations.")),
                Paragraph(Text("For every graph member (u,g) and every complex smooth compactly supported eta, the integral of g_Z times conjugate eta equals minus the integral of u times conjugate partial_z eta. The quantifiers include zero states, arbitrary angular dependence and unbounded state support. L2 pairing makes both integrals finite. This identifies the actual closed central component as the distributional central derivative.")),
                Paragraph(Text("For every member of this actual graph, g_Z = 0 if and only if u = 0 in L2. For the forward direction, the distributional Fourier derivative formula forces the central-frequency coordinate times the L2 Fourier transform to vanish as a distribution. Multiplication by that coordinate preserves local integrability, so compact-test separation makes the product vanish almost everywhere. The central-frequency hyperplane is a proper real linear subspace and has Lebesgue measure zero. The entire Fourier transform therefore vanishes in L2, and Fourier inversion gives u = 0. The reverse direction follows from the already established single-valued graph. This treats the zero-frequency hyperplane and all spatial tails without imposing compact support on u or restricting its angular modes.")),
                Paragraph(Text("Mathlib uses the Fourier character exp(-2*pi*i*inner(x,xi)), whereas the source central partial Fourier convention uses exp(-i*k*z). The distributional multiplier in this proof is consequently 2*pi*i*xi_z, and k = 2*pi*xi_z. Its nonzero scalar factor is removed explicitly. The proof uses the full L2 Fourier isometry and requires no L1 hypothesis or one-dimensional Fourier identification.")),
                Paragraph(Text("For the source's Corollary 11.2, the kernel conclusion supplies positive central energy for a nonzero member of the original H1 graph. The separate horizontal full-Green bound, the positive finite full-clock Green denominator, the sharp infimum and optimal coefficient remain additional obligations. Only together with their respective proofs can these imply the original strict inequality and nonattainment. This result provides no positive uniform spectral gap, minimizing profile, physical realization, response rank, spatial dimension or higher-contact conclusion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula space = Constant("Space"), state = Constant("State"), ambient = Constant("Ambient");
        Formula core = Constant("compactCore"), graph = Constant("jointGraph");
        Formula coreOperator = Constant("coreOperator"), closedOperator = Constant("closedOperator");
        Formula volume = Constant("volume"), indices = Call("Fin", D(3));
        Formula functions = new Formula.TypeArrow(space, complex);
        Formula p = F.Id("p"), q = F.Id("q"), s = F.Id("s"), n = F.Id("n");
        Formula i = F.Id("i"), e = F.Id("e"), f = F.Id("f"), x = F.Id("x");
        Formula pState = Call("fst", p), pComponents = Call("snd", p);
        Formula jet = Call("coreJet", Apply(s, n));
        Formula approximation = Exists("s", new Formula.TypeArrow(natural, core),
            And(Call("Tendsto", new Formula.Sequence(Call("fst", jet), n, natural),
                    Constant("atTop"), Call("nhds", pState)),
                All("i", indices,
                    Call("Tendsto", new Formula.Sequence(Apply(Call("snd", jet), i), n, natural),
                        Constant("atTop"), Call("nhds", Apply(pComponents, i))))));
        Formula singleValued = All("p", ambient, Implies(Member(p, graph),
            All("q", ambient, Implies(Member(q, graph),
                Implies(Equal(pState, Call("fst", q)), Equal(pComponents, Call("snd", q)))))));
        Formula weakIdentity = Equal(
            Integral(Mul(Apply(Call("rep", Apply(pComponents, D(2))), x),
                Call("conj", Apply(e, x))), space, volume),
            new Formula.Negate(Integral(Mul(Apply(Call("rep", pState), x),
                Call("conj", Call("fderiv", real, e, x, Call("axis", D(2))))), space, volume)));
        Formula weakCentral = All("p", ambient, Implies(Member(p, graph),
            All("e", functions, Implies(Call("ContDiff", real, Constant("smoothOrder"), e),
                Implies(Call("HasCompactSupport", e), weakIdentity)))));
        Formula zeroState = new Formula.Subscript(D(0), state);
        Formula kernel = All("p", ambient, Implies(Member(p, graph),
            Iff(Equal(Apply(pComponents, D(2)), zeroState), Equal(pState, zeroState))));
        Formula coreInclusion = All("f", functions,
            Implies(Call("ContDiff", real, Constant("smoothOrder"), f),
                Implies(Call("HasCompactSupport", f),
                    Exists("p", ambient, And(Member(p, graph),
                        And(Call("EventuallyEq", Call("ae", volume), Call("rep", pState), f),
                            All("i", indices,
                                Call("EventuallyEq", Call("ae", volume),
                                    Call("rep", Apply(pComponents, i)),
                                    new Formula.Sequence(Call("fderiv", real, f, x,
                                        Call("frame", i, x)), x, space)))))))));
        return And(Call("Dense", Call("domain", coreOperator)),
            And(Call("IsClosable", coreOperator),
                And(Call("IsClosed", closedOperator),
                    And(Equal(Call("graph", closedOperator), graph),
                        And(All("p", ambient, Iff(Member(p, graph), approximation)),
                            And(singleValued, And(weakCentral, And(kernel, coreInclusion))))))));
    }

    private static Formula Constant(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Integral(Formula expression, Formula space, Formula volume) =>
        Seq(Int, Underscore, Grp(F.Id("x"), Colon, Sp, space), Sp,
            Open, expression, Close, Sp, Mathrm, Grp(F.Id("d")), Sp, volume);
}
