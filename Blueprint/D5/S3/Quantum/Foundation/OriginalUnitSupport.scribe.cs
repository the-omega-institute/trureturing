using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalUnitSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalUnitSupport.";

    public DocumentDefinition Create()
    {
        Formula field = F.Id("F"), index = F.Id("iota"), space = F.Id("V"),
            cone = F.Id("C"), rho = F.Id("rho"), unit = F.Id("u"),
            x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrices = Call("Matrix", index, index, field);
        Formula vectors = Seq(index, To, Sp, field);
        Formula linear(Formula target) => Call("LinearMap", real, space, target);
        Formula app(Formula f, Formula a) => Seq(f, Open, a, Close);
        Formula mat(Formula a) => app(rho, a);
        Formula action(Formula a) => Call("mulVec", mat(a), z);
        Formula support = Call("commonSupport", cone, rho);
        Formula parameters(Formula body) => All("F", F.Id("Type"),
            All("iota", F.Id("Type"), All("V", F.Id("Type"), Seq(
                Bracket(Call("RCLike", field)), Sp,
                Bracket(Call("Fintype", index)), Sp,
                Bracket(Call("DecidableEq", index)), Sp,
                Bracket(Call("AddCommGroup", space)), Sp,
                Bracket(Call("Module", real, space)), Sp, body))));
        Formula objects(Formula body) => All("C", Call("PointedCone", real, space),
            All("rho", linear(matrices), body));
        Formula kernel = All("z", vectors, IffF(Eq(action(y), D(0)),
            All("x", space, Eq(action(x), D(0)))));
        Formula nativeVector = Call("ofLp", z);
        Formula positive = All("z", Call("EuclideanSpace", field, index),
            Imp(Member(z, support), Imp(Seq(z, Neq, Sp, D(0)),
                LtF(D(0), Call("re", Call("dotProduct", Call("star", nativeVector),
                    Call("mulVec", mat(y), nativeVector)))))));
        Formula conclusion = Ex("y", space, And(Member(y, cone),
            And(Eq(app(unit, y), D(1)), And(kernel,
                And(Eq(Call("range", Call("toEuclideanLin", mat(y))), support), positive)))));
        Formula statement = parameters(Seq(
            Bracket(Call("FiniteDimensional", real, space)), Sp,
            Bracket(Call("Nontrivial", space)), Sp,
            All("C", Call("PointedCone", real, space),
                Imp(Eq(Call("span", real, cone), Call("top", Call("Submodule", real, space))),
                    All("u", linear(real),
                        Imp(All("x", space, Imp(Member(x, cone),
                            Imp(Seq(x, Neq, Sp, D(0)), LtF(D(0), app(unit, x))))),
                            All("rho", linear(matrices),
                                Imp(Call("Injective", rho),
                                    Imp(All("x", space, Imp(Member(x, cone),
                                        Call("PosSemidef", mat(x)))), conclusion)))))))));
        Formula dimension = Call("finrank", field, support);
        Formula nIndex = Call("Fin", dimension);
        Formula nativeMatrices = Call("Matrix", nIndex, nIndex, field);
        Formula inclusion = F.Id("U"), sigma = F.Id("sigma"), m = F.Id("m"),
            v = F.Id("v"), t = F.Id("t");
        Formula sigmaAt(Formula a) => app(sigma, a);
        Formula mul(Formula a, Formula b) => Call("mul", a, b);
        Formula adjoint(Formula a) => Call("conjTranspose", a);
        Formula inv(Formula a) => Call("inv", a);
        Formula det(Formula a) => Call("det", a);
        Formula delta(Formula a) => Call("re", det(a));
        Formula massSlice(Formula mass) => Call("setOf", Seq(x, Mapsto, Sp,
            And(Member(x, cone), Eq(app(unit, x), mass))));
        Formula compactBase = Call("IsCompact", massSlice(D(1)));
        Formula nativeInputs(Formula body, bool compact)
        {
            Formula tail = All("rho", linear(matrices), Imp(Call("Injective", rho),
                Imp(All("x", space, IffF(Member(x, cone), Call("PosSemidef", mat(x)))), body)));
            if (compact) tail = Imp(compactBase, tail);
            tail = All("u", linear(real), Imp(All("x", space, Imp(Member(x, cone),
                Imp(Seq(x, Neq, Sp, D(0)), LtF(D(0), app(unit, x))))), tail));
            tail = All("C", Call("PointedCone", real, space),
                Imp(Eq(Call("span", real, cone), Call("top", Call("Submodule", real, space))), tail));
            Formula topological = compact ? Seq(
                Bracket(Call("TopologicalSpace", space)), Sp,
                Bracket(Call("IsTopologicalAddGroup", space)), Sp,
                Bracket(Call("ContinuousSMul", real, space)), Sp,
                Bracket(Call("T2Space", space)), Sp) : Bracket(Call("Nontrivial", space));
            return compact
                ? parameters(Seq(Bracket(Call("FiniteDimensional", real, space)), Sp,
                    Bracket(Call("Nontrivial", space)), Sp, topological, tail))
                : parameters(Seq(Bracket(Call("FiniteDimensional", real, space)), Sp,
                    Bracket(Call("Nontrivial", space)), Sp, tail));
        }
        Formula compressionLaws = Chain(
            Eq(mul(adjoint(inclusion), inclusion), D(1)),
            Eq(Call("range", Call("toEuclideanLin", inclusion)), support),
            All("x", space, Eq(sigmaAt(x), mul(mul(adjoint(inclusion), mat(x)), inclusion))),
            All("x", space, Eq(mat(x), mul(mul(inclusion, sigmaAt(x)), adjoint(inclusion)))),
            Call("Injective", sigma), All("x", space, Call("IsHermitian", sigmaAt(x))),
            All("x", space, IffF(Member(x, cone), Call("PosSemidef", sigmaAt(x)))),
            All("x", space, Eq(Call("rank", sigmaAt(x)), Call("rank", mat(x)))));
        Formula coordinateWitness(Formula laws) => And(LtF(D(0), dimension),
            Ex("U", Call("Matrix", index, nIndex, field),
                Ex("sigma", Call("LinearMap", real, space, nativeMatrices), laws)));
        Formula supportState = Ex("y", space, Chain(Member(y, cone),
            Eq(app(unit, y), D(1)), Call("PosDef", sigmaAt(y))));
        Formula compressionStatement = nativeInputs(coordinateWitness(
            And(compressionLaws, supportState)), false);
        Formula maximum = All("x", space, Imp(Member(x, cone),
            Imp(Eq(app(unit, x), dimension),
                new Formula.Relation(delta(sigmaAt(x)), FormulaRelationOperator.LessThanOrEqual,
                    delta(sigmaAt(m))))));
        Formula affine = Call("add", m, Call("smul", t, v));
        Formula variation = All("v", space, Call("HasDerivAt",
            Seq(t, Colon, Sp, real, Mapsto, Sp, delta(sigmaAt(affine))),
            mul(delta(sigmaAt(m)), Call("re", Call("trace", mul(inv(sigmaAt(m)), sigmaAt(v))))), D(0)));
        Formula root = Call("sqrt", inv(sigmaAt(m)));
        Formula rootLaws = Chain(Call("IsHermitian", root), Call("IsUnit", root),
            Eq(mul(root, root), inv(sigmaAt(m))), Eq(mul(mul(root, sigmaAt(m)), root), D(1)));
        Formula maximizer = Ex("m", space, Chain(Member(m, cone),
            Eq(app(unit, m), dimension), Call("PosDef", sigmaAt(m)),
            LtF(D(0), delta(sigmaAt(m))), maximum, variation, rootLaws));
        Formula maximumStatement = nativeInputs(coordinateWitness(Chain(compressionLaws,
            Call("IsCompact", Call("image", sigma, massSlice(dimension))), maximizer)), true);
        Formula inverseTrace = All("v", space,
            Eq(Call("trace", mul(inv(sigmaAt(m)), sigmaAt(v))), app(unit, v)));
        Formula k = F.Id("k");
        Formula maximumAt(Formula point) => All("x", space, Imp(Member(x, cone),
            Imp(Eq(app(unit, x), dimension),
                new Formula.Relation(delta(sigmaAt(x)), FormulaRelationOperator.LessThanOrEqual,
                    delta(sigmaAt(point))))));
        Formula uniqueMaximum = All("k", space, Imp(Member(k, cone),
            Imp(Eq(app(unit, k), dimension), Imp(maximumAt(k), Eq(k, m)))));
        Formula stationarity = Ex("m", space, Chain(Member(m, cone),
            Eq(app(unit, m), dimension), Call("PosDef", sigmaAt(m)), inverseTrace,
            maximum, uniqueMaximum));
        Formula stationarityStatement = nativeInputs(coordinateWitness(
            Chain(compressionLaws, stationarity)), true);
        Formula psi = F.Id("Psi"), matrixX = F.Id("X");
        Formula psiAt(Formula a) => app(psi, a);
        Formula inverseCongruence = All("v", space, Eq(mat(v),
            mul(mul(inclusion, mul(mul(inv(root), psiAt(v)), inv(root))), adjoint(inclusion))));
        Formula normalizedBase = Eq(Call("image", psi, massSlice(D(1))),
            Call("setOf", Seq(matrixX, Mapsto, Sp, Chain(
                Member(matrixX, Call("range", psi)), Call("PosSemidef", matrixX),
                Eq(Call("trace", matrixX), D(1))))));
        Formula e = F.Id("e"), f = F.Id("f"), g = F.Id("g"), j = F.Id("j"),
            p = F.Id("p"), r = F.Id("r");
        Formula range = Call("range", psi);
        Formula rangeDual = Call("LinearMap", real, range, real);
        Formula dual = Call("dualMap", Call("symm", e));
        Formula value(Formula a) => Call("val", a);
        Formula le(Formula a, Formula b) =>
            new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
        Formula setOf(Formula a, Formula body) => Call("setOf", Seq(a, Mapsto, Sp, body));
        Formula properOriginal(Formula a) => All("v", space, Imp(Member(v, cone),
            And(le(D(0), app(a, v)), le(app(a, v), app(unit, v)))));
        Formula properNormalized(Formula a) => All("X", range,
            Imp(Call("PosSemidef", value(matrixX)),
                And(le(D(0), app(a, matrixX)),
                    le(app(a, matrixX), Call("re", Call("trace", value(matrixX)))))));
        Formula baseOriginal = massSlice(D(1));
        Formula baseNormalized = setOf(matrixX, And(Call("PosSemidef", value(matrixX)),
            Eq(Call("trace", value(matrixX)), D(1))));
        Formula originalReadings = setOf(r, Ex("f", linear(real), Chain(properOriginal(f),
            Eq(app(f, p), D(1)), Eq(app(f, x), r))));
        Formula normalizedReadings = setOf(r, Ex("g", rangeDual, Chain(properNormalized(g),
            Eq(app(g, app(e, p)), D(1)), Eq(app(g, app(e, x)), r))));
        Formula originalMinimizers = setOf(f, Chain(properOriginal(f), Eq(app(f, p), D(1)),
            All("j", linear(real), Imp(properOriginal(j), Imp(Eq(app(j, p), D(1)),
                le(app(f, x), app(j, x)))))));
        Formula normalizedMinimizers = setOf(g, Chain(properNormalized(g),
            Eq(app(g, app(e, p)), D(1)), All("j", rangeDual, Imp(properNormalized(j),
                Imp(Eq(app(j, app(e, p)), D(1)),
                    le(app(g, app(e, x)), app(j, app(e, x))))))));
        Formula aSet = F.Id("A"), bSet = F.Id("B"), fSet = F.Id("F"),
            gSet = F.Id("G"), sSet = F.Id("S");
        Formula setSpace = Call("Set", space), setRange = Call("Set", range);
        Formula subset(Formula a, Formula b) => Call("Subset", a, b);
        Formula minimalOriginal = setOf(v, All("F", setSpace,
            Imp(Call("Convex", real, fSet), Imp(Call("IsExtreme", real, aSet, fSet),
                Imp(subset(sSet, fSet), Member(v, fSet))))));
        Formula minimalNormalized = setOf(matrixX, All("G", setRange,
            Imp(Call("Convex", real, gSet),
                Imp(Call("IsExtreme", real, Call("image", e, aSet), gSet),
                    Imp(subset(Call("image", e, sSet), gSet), Member(matrixX, gSet))))));
        Formula transport = Ex("e", Call("LinearEquiv", real, space, range), Chain(
            All("v", space, Eq(value(app(e, v)), psiAt(v))),
            Eq(Call("image", e, baseOriginal), baseNormalized),
            Eq(Call("image", e, Call("extremePoints", baseOriginal, real)),
                Call("extremePoints", baseNormalized, real)),
            All("F", setSpace, IffF(Call("Convex", real, fSet),
                Call("Convex", real, Call("image", e, fSet)))),
            All("A", setSpace, All("B", setSpace,
                IffF(Call("IsExtreme", real, aSet, bSet),
                    Call("IsExtreme", real, Call("image", e, aSet), Call("image", e, bSet))))),
            All("A", setSpace, All("S", setSpace,
                Eq(Call("image", e, minimalOriginal), minimalNormalized))),
            All("f", linear(real), IffF(properOriginal(f), properNormalized(app(dual, f)))),
            All("p", space, Eq(Call("image", dual,
                setOf(f, And(properOriginal(f), Eq(app(f, p), D(1))))),
                setOf(g, And(properNormalized(g), Eq(app(g, app(e, p)), D(1)))))),
            All("p", space, All("x", space, Eq(originalReadings, normalizedReadings))),
            All("p", space, All("x", space,
                Eq(Call("image", dual, originalMinimizers), normalizedMinimizers)))));
        Formula singleton = Call("singleton", m);
        Formula oneDimensional = Imp(Eq(dimension, D(1)), Chain(
            Eq(baseOriginal, singleton),
            Eq(Call("extremePoints", baseOriginal, real), singleton),
            Eq(setOf(f, And(properOriginal(f), Eq(app(f, m), D(1)))),
                Call("singleton", unit)),
            Eq(setOf(v, And(Member(v, baseOriginal), Ex("f", linear(real),
                Chain(properOriginal(f), Eq(app(f, m), D(1)), Eq(app(f, v), D(0)))))),
                Call("emptySet")),
            Eq(setOf(f, properOriginal(f)), setOf(f, Ex("t", real,
                Chain(le(D(0), t), le(t, D(1)), Eq(f, Call("smul", t, unit))))))));
        Formula decomp(Formula map, Formula point) => Ex("k", Call("Nat"),
            Ex("y", Seq(Call("Fin", k), To, Sp, space), Chain(
                All("j", Call("Fin", k), And(Member(app(y, j), cone),
                    Eq(Call("rank", app(map, app(y, j))), D(1)))),
                Eq(app(map, point), Call("sum", Seq(j, Mapsto, Sp, app(map, app(y, j))))))));
        Formula rogTransport = All("x", space, Imp(Member(x, cone),
            IffF(decomp(rho, x), decomp(psi, x))));
        Formula singletonRog = Imp(Ex("p", space, Eq(baseOriginal, Call("singleton", p))),
            Imp(All("x", space, Imp(Member(x, cone), decomp(rho, x))), Eq(dimension, D(1))));
        Formula normalizedWitness = Ex("m", space, Chain(Member(m, cone),
            Eq(app(unit, m), dimension), Call("PosDef", sigmaAt(m)), inverseTrace,
            maximum, uniqueMaximum, Call("IsHermitian", root), Call("IsUnit", root),
            Eq(mul(root, root), inv(sigmaAt(m))),
            All("v", space, Eq(psiAt(v), mul(mul(root, sigmaAt(v)), root))),
            Eq(psiAt(m), D(1)), Call("Injective", psi),
            All("v", space, Call("IsHermitian", psiAt(v))),
            All("v", space, Eq(Call("trace", psiAt(v)), app(unit, v))),
            All("v", space, IffF(Member(v, cone), Call("PosSemidef", psiAt(v)))),
            All("v", space, Eq(Call("rank", psiAt(v)), Call("rank", mat(v)))),
            inverseCongruence, Member(D(1), Call("range", psi)), normalizedBase, rogTransport, singletonRog, oneDimensional, transport));
        Formula normalizationStatement = nativeInputs(And(LtF(D(0), dimension),
            Ex("U", Call("Matrix", index, nIndex, field),
                Ex("sigma", Call("LinearMap", real, space, nativeMatrices),
                    Ex("Psi", Call("LinearMap", real, space, nativeMatrices),
                        Chain(compressionLaws, normalizedWitness))))), true);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Native support compression produces an actual original-unit positive determinant maximizer.",
            H("Original unit, native support and determinant maximization"), Blocks(
                Paragraph(Text("Let F be a real or complex scalar field, represented by RCLike, and let iota be any finite decidable matrix index type. V is a nonzero finite dimensional real vector space. C is a pointed cone whose real linear span is V. The real linear map rho is injective and sends every member of C to a positive semidefinite native F-matrix. The original real linear unit u is strictly positive on every nonzero member of C. No trace normalization, positive definite ambient representative, rank-one generation, closedness, or compactness is needed for this support result.")),
                Describe.Lean(DescribeId.Create("common-support"),
                    DeclarationHandle.Create(Owner + "commonSupport"), H("Native common support"),
                    StatementSource.FromAuthor(Disp(parameters(objects(Eq(support,
                        Call("iSup", Seq(x, InMacro, Sp, cone, Mapsto, Sp,
                            Call("range", Call("toEuclideanLin", mat(x)))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The supremum is in the lattice of F-linear subspaces of EuclideanSpace F iota and ranges over every original cone element. Thus a complex support has its complex dimension; it is not a realification. toEuclideanLin is the matrix action in the usual orthonormal coordinates."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-unit-full-support"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_full_support"),
                    H("An original state with the entire common support"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Finite dimensionality selects a finite spanning subset of the original cone. For its sum a, positive semidefiniteness makes a zero quadratic value force each summand to annihilate the same vector. Real spanning then propagates this annihilation to every represented original vector. Injectivity and nontriviality ensure a is nonzero. Hence u(a) is strictly positive and y = a / u(a) is an actual original state with exactly the same kernel. Hermitian orthogonal range-kernel duality identifies its range with the entire common support. A nonzero vector in that support has strictly positive quadratic value: otherwise it belongs to both the range and its orthogonal complement. This allows support-deficient ambient representations and includes support dimension one. ofLp denotes the ordinary coordinate vector of a Euclidean vector; re is the real part."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-unit-support-compression"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_support_compression"),
                    H("Faithful native coordinates on the entire common support"),
                    StatementSource.FromAuthor(Disp(compressionStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The support dimension n is finrank over F, with no complex realification. U consists of an orthonormal basis of the entire common support. Real generation extends range containment and Hermitian symmetry from cone elements to every original vector. U adjoint U is the identity, and the common-support projection fixes every original matrix on both sides, giving whole-V reconstruction. Compression sigma is therefore injective. Rectangular congruence in both directions gives the exact PSD section, and the two factorizations give equality of native F-ranks. The original-unit state from the preceding producer compresses to a positive definite matrix. No ambient full-support or normalized-section hypothesis is imposed. The theorem returns n positive and includes n equal to one."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-unit-determinant-maximum"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_determinant_maximum"),
                    H("An actual positive determinant maximum and its affine variation"),
                    StatementSource.FromAuthor(Disp(maximumStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Retain the same compression laws and assume the entire original unit-one base is compact in the finite dimensional Hausdorff real vector topology. The mass-n original slice is exactly n times this base, so its sigma image is compact. Scaling the produced unit-one state by n gives an actual positive definite competitor. Continuity of the real part of the native determinant supplies a global maximum at M = sigma(m). The competitor makes its real determinant strictly positive; the exact PSD section then makes M positive definite. Every original feasible vector participates in the maximum comparison. For every original v, including indefinite represented directions, the real derivative of det sigma(m + t v) at zero is Re(det M) times Re tr(M inverse sigma(v)). This derivative is not asserted to vanish. It directly reuses the pinned polynomial determinant derivative at the identity, restricts scalars to the real line, and factors out M. The principal inverse square root S = CFC.sqrt(M inverse) is Hermitian and invertible, satisfies S squared = M inverse and S M S = I. These are ambient matrix identities and require no square-root or inverse closure of the image section."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-unit-inverse-trace-stationarity"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_inverse_trace_stationarity"),
                    H("Full original-vector inverse-trace stationarity"),
                    StatementSource.FromAuthor(Disp(stationarityStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The determinant maximum admits a two-sided positive-definite neighborhood in every original direction whose unit value is zero. Its real determinant derivative therefore vanishes on the kernel of the original unit. Decomposing an arbitrary original vector into a kernel direction plus its mass multiple, and using the nonzero support dimension, extends the identity to every original vector: trace((sigma(m)) inverse sigma(v)) equals u(v), with the trace taken in the native real or complex support coordinates. The same point is the unique global determinant maximum on the entire original mass-n slice. For any second maximum, the same local variation proves the second inverse-trace identity. The trace of the Gram matrix of the difference sandwiched by the two principal inverse square roots is zero: its expansion is the sum of the two cross inverse-traces minus twice the support dimension. The trace-Gram zero criterion and invertibility force equality, including equality of the original vectors by injectivity. No positive definite representative of the dual unit or normalized section is assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-unit-normalization"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_normalization"),
                    H("Actual original-unit normalization on the entire original carrier"),
                    StatementSource.FromAuthor(Disp(normalizationStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Use the very same compressed original mass-n point h supplied by inverse-trace stationarity. Its unique determinant maximum and principal inverse square root S define the real-linear map Psi(v) = S sigma(v) S on every original vector. Cyclicity of trace and S squared = sigma(h) inverse give trace Psi(v) = u(v), while S sigma(h) S = I makes the identity an actual member of this same image. Invertibility of S reconstructs sigma and then the original rho from every Psi(v); hence Psi is faithful. Congruence preserves Hermitian symmetry, the exact entire PSD cone section and native matrix rank. The image of the entire original unit-one base is exactly the positive trace-one part of this same linear image. No ambient dual lift is inverted and no normalized-section hypothesis is introduced. For each original cone element, finite decompositions into original native rank-one positive matrices correspond under the same Psi, retaining each original summand. Thus the entire ROG property transports in both directions. If the original base is a singleton and the cone is ROG, an actual rank-one summand of the full-support point is a positive multiple of that point. Its compressed matrix is positive definite and has rank n, forcing n = 1. The equivalence e from the original space onto the range of this same Psi carries the entire base and all its extreme points to the positive trace-one base in that range. It preserves convexity and every extreme subset, for arbitrary ambient subsets. It consequently carries the entire intersection of convex extreme subsets containing any prescribed set onto the corresponding intersection. This includes the entire minimal faces of both the original cone and its base. Its contravariant dual d(f) = f composed with e inverse carries the entire proper interval and each full confirmer set bijectively. For every original p and x, the sets of attainable confirming readings agree exactly, so their lower envelopes agree and d maps all minimizers onto all minimizers. In particular every actual zero confirmer transports in both directions, even when different zero conditions initially have different confirmers. Only elements of the actual image are passed to e inverse. When n is one, the original base and its entire extreme-point set are both the singleton containing the same h. Generation and strict positivity show every cone vector is its original mass times h. Thus every original effect is t times u with t in the closed unit interval, the only confirmer of h is u, and its entire exclusion set is empty. No division by n minus one occurs."))),
                    DescribeRole.Theorem),
                Paragraph(Text("The complete source normalization-and-transport target remains unresolved. The rank-one description of all pure points under ROG, compressed real/complex codimension, annihilator congruence and same-frame complement conclusions still require proofs. The established reading-set and minimizer transport does not yet prove existence of a comparison minimum from the original effect interval. The dimension-one singleton-base, entire effect interval and empty-exclusion return, and the converse from a singleton ROG base to support dimension one, are included. Classification and physical realization are not inferred. The linear-algebra, compact-extremum, polynomial-derivative and functional-calculus tools are standard; no literature priority is claimed.")))));
    }

    private static Formula Chain(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (int i = formulas.Length - 2; i >= 0; --i) result = And(formulas[i], result);
        return result;
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Member(Formula left, Formula right) => Seq(left, InMacro, Sp, right);
    private static Formula LtF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Bracket(Formula body) => Seq(OpenBracket, body, CloseBracket);
}
