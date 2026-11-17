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
        Formula rootMatrix = F.Id("A");
        Formula sqrtLawsStatement = All("F", F.Id("Type"), All("iota", F.Id("Type"), Seq(
            Bracket(Call("RCLike", field)), Sp, Bracket(Call("Fintype", index)), Sp,
            Bracket(Call("DecidableEq", index)), Sp,
            All("A", matrices, Imp(Call("PosDef", rootMatrix), Chain(
                Call("IsHermitian", Call("sqrt", inv(rootMatrix))),
                Call("IsUnit", Call("sqrt", inv(rootMatrix))),
                Eq(mul(Call("sqrt", inv(rootMatrix)), Call("sqrt", inv(rootMatrix))), inv(rootMatrix)),
                Eq(mul(mul(Call("sqrt", inv(rootMatrix)), rootMatrix), Call("sqrt", inv(rootMatrix))), D(1))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Native support compression produces an actual maximizer and full-vector stationarity.",
            H("Original unit, native support and stationarity"), Blocks(
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
                Describe.Lean(DescribeId.Create("principal-inverse-sqrt-laws"),
                    DeclarationHandle.Create(Owner + "principal_inverse_sqrt_laws"),
                    H("Shared principal inverse square root laws"),
                    StatementSource.FromAuthor(Disp(sqrtLawsStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For a positive definite native real or complex matrix A, the principal square root of its inverse is Hermitian and invertible. Its square is A inverse, and its congruence sends A to the identity. These identities give the inverse square roots used in determinant maximization, inverse cross-trace uniqueness and original-unit normalization."))),
                    DescribeRole.Theorem))));
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
