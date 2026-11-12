using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalUnitNormalizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalUnitNormalization.";

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
                Eq(Call("image", dual, originalMinimizers), normalizedMinimizers))),
            Call("NativeGeometry", cone, unit, psi, m), Call("OriginalEffectGeometry", cone, unit),
            Call("NativeAmbientDimensions", dimension), Call("NativeCongruence", sigma, psi, root)));
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
        Formula nativeGeometry(Formula ni, Formula map)
        {
            Formula hm = Call("HermitianMat", ni, field), hmap = F.Id("H"),
                hx = F.Id("X"), hb = F.Id("b"), hy = F.Id("y"), hi = F.Id("i"),
                hj = F.Id("j"), card = Call("card", ni);
            Formula hrange = Call("range", hmap), hpure = Call("extremePoints", baseOriginal, real);
            Formula rankOne(Formula q) => Call("rankOne", q);
            Formula complement = Call("smul", inv(Call("sub", card, D(1))), Call("sub", m, p));
            Formula nativeBase = setOf(hx, Chain(Member(hx, hrange), le(D(0), hx),
                Eq(Call("trace", hx), D(1))));
            Formula rankDecomposition = All("x", space, Imp(Member(x, cone), decomp(map, x)));
            Formula frames = All("p", space, Imp(Member(p, hpure), All("i", ni,
                Ex("b", Call("OrthonormalBasis", ni, field, Call("EuclideanSpace", field, ni)),
                    Ex("y", Seq(ni, To, Sp, space), Chain(Eq(app(hy, hi), p),
                        All("j", ni, And(Member(app(hy, hj), hpure),
                            Eq(app(hmap, app(hy, hj)), rankOne(app(hb, hj))))),
                        Eq(Call("sum", hy), m)))))));
            return Ex("H", Call("LinearMap", real, space, hm), Chain(
                All("v", space, Eq(Call("mat", app(hmap, v)), app(map, v))),
                Eq(Call("image", hmap, baseOriginal), nativeBase),
                Imp(rankDecomposition, Chain(Call("ROG", hrange),
                    Eq(Call("image", hmap, hpure), Call("pureRanks", hrange)),
                    All("p", space, Imp(Member(p, hpure), And(le(app(hmap, p), D(1)),
                        Imp(LtF(D(1), card), And(Member(complement, baseOriginal),
                            Eq(app(hmap, complement), Call("smul", inv(Call("sub", card, D(1))),
                                Call("sub", D(1), app(hmap, p))))))))), frames))));
        }
        Formula genericPsi = Call("LinearMap", real, space, matrices);
        Formula nativeGeometryStatement = parameters(All("C", Call("PointedCone", real, space),
            All("u", linear(real), All("Psi", genericPsi, All("m", space,
                IffF(Call("NativeGeometry", cone, unit, psi, m), nativeGeometry(index, psi)))))));
        Formula coeFn = F.Id("coeFn");
        Formula allEffects = Call("image", coeFn, setOf(f, properOriginal(f)));
        Formula allConfirmers = Call("image", coeFn,
            setOf(f, And(properOriginal(f), Eq(app(f, p), D(1)))));
        Formula minReadings = setOf(r, Ex("g", linear(real),
            Chain(properOriginal(g), Eq(app(g, p), D(1)), Eq(app(g, x), r))));
        Formula attained = Ex("f", linear(real), Chain(properOriginal(f), Eq(app(f, p), D(1)),
            All("g", linear(real), Imp(properOriginal(g), Imp(Eq(app(g, p), D(1)),
                le(app(f, x), app(g, x))))),
            Eq(app(f, x), Call("sInf", minReadings)),
            Imp(Member(x, cone), IffF(Eq(app(f, x), D(0)),
                Ex("g", linear(real), Chain(properOriginal(g), Eq(app(g, p), D(1)),
                    Eq(app(g, x), D(0))))))));
        Formula effectGeometry = Chain(Call("IsCompact", allEffects),
            All("p", space, Imp(Eq(app(unit, p), D(1)), Chain(
                Call("IsCompact", allConfirmers), Call("Nonempty", allConfirmers),
                All("x", space, attained)))));
        Formula effectGeometryStatement = All("V", F.Id("Type"), Seq(
            Bracket(Call("AddCommGroup", space)), Sp, Bracket(Call("Module", real, space)), Sp,
            All("C", Call("PointedCone", real, space), All("u", linear(real),
                IffF(Call("OriginalEffectGeometry", cone, unit),
                    Call("let", Eq(coeFn, Seq(f, Mapsto, Sp, Call("coe", f))), effectGeometry))))));
        Formula complex = Seq(Mathbb, Grp(F.Id("C"))), ambientN = F.Id("n"), ell = F.Id("L");
        Formula ambient(Formula scalar) => Call("HermitianMat", Call("Fin", ambientN), scalar);
        Formula rank(Formula carrier) => Call("finrank", real, carrier);
        Formula perp(Formula carrier) => Call("orthogonal", carrier);
        Formula add(Formula a, Formula b) => Call("add", a, b);
        Formula realDim = Call("div", mul(ambientN, add(ambientN, D(1))), D(2));
        Formula complexDim = Call("pow", ambientN, D(2));
        Formula dimensionsStatement = All("n", Call("Nat"), IffF(
            Call("NativeAmbientDimensions", ambientN), Chain(
                Eq(rank(ambient(real)), realDim), Eq(rank(ambient(complex)), complexDim),
                All("L", Call("Submodule", real, ambient(real)),
                    Eq(add(rank(ell), rank(perp(ell))), realDim)),
                All("L", Call("Submodule", real, ambient(complex)),
                    Eq(add(rank(ell), rank(perp(ell))), complexDim)))));
        Formula hmAmbient = Call("HermitianMat", index, field),
            hzero = F.Id("H"), hone = F.Id("J"), equiv = F.Id("E"),
            aa = F.Id("A"), bb = F.Id("B"), congruent = F.Id("S");
        Formula hmat(Formula a) => Call("mat", a);
        Formula ep(Formula a) => app(equiv, a);
        Formula ei(Formula a) => app(Call("symm", equiv), a);
        Formula ip(Formula a, Formula b) => Call("inner", real, a, b);
        Formula trre(Formula a) => Call("re", Call("trace", a));
        Formula hzrange = Call("range", hzero), horange = Call("range", hone);
        Formula congruenceBody = Ex("H", linear(hmAmbient), Ex("J", linear(hmAmbient),
            Ex("E", Call("LinearEquiv", real, hmAmbient, hmAmbient), Chain(
                All("v", space, Eq(hmat(app(hzero, v)), sigmaAt(v))),
                All("v", space, Eq(hmat(app(hone, v)), psiAt(v))),
                All("A", hmAmbient,
                    Eq(hmat(ep(aa)), mul(mul(congruent, hmat(aa)), congruent))),
                All("A", hmAmbient,
                    Eq(hmat(ei(aa)), mul(mul(inv(congruent), hmat(aa)), inv(congruent)))),
                All("v", space, Eq(app(hone, v), ep(app(hzero, v)))),
                Eq(horange, Call("map", hzrange, Call("toLinearMap", equiv))),
                Eq(rank(perp(hzrange)), rank(perp(horange))),
                All("A", hmAmbient, All("B", hmAmbient,
                    Eq(ip(ep(aa), bb), ip(aa, ep(bb))))),
                All("A", hmAmbient, All("v", space,
                    Eq(trre(mul(hmat(aa), psiAt(v))), trre(mul(hmat(ep(aa)), sigmaAt(v)))))),
                All("A", hmAmbient,
                    IffF(Member(aa, perp(horange)), Member(ep(aa), perp(hzrange)))),
                All("A", hmAmbient,
                    IffF(Member(aa, perp(hzrange)), Member(ei(aa), perp(horange))))))));
        Formula congruenceStatement = parameters(All("sigma", genericPsi,
            All("Psi", genericPsi, All("S", matrices,
                IffF(Call("NativeCongruence", sigma, psi, congruent), congruenceBody)))));
        Formula normalizationStatement = nativeInputs(And(LtF(D(0), dimension),
            Ex("U", Call("Matrix", index, nIndex, field),
                Ex("sigma", Call("LinearMap", real, space, nativeMatrices),
                    Ex("Psi", Call("LinearMap", real, space, nativeMatrices),
                        Chain(compressionLaws, normalizedWitness))))), true);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Native support compression produces actual original-unit normalization and geometric transport.",
            H("Original-unit normalization and entire original geometry"), Blocks(
                Paragraph(Text("Retain the native real or complex field and the arbitrary nonzero finite-dimensional real original carrier. The generating pointed cone has an arbitrary strictly positive original unit, a compact entire unit-one base, and a faithful real-linear representation whose whole PSD section equals the original cone. OriginalUnitSupport supplies the native compression and unique determinant maximizer. The same original point and principal inverse square root normalize every original vector. No ambient full support or original trace unit is assumed.")),
                Describe.Lean(DescribeId.Create("native-original-geometry"),
                    DeclarationHandle.Create(Owner + "NativeGeometry"),
                    H("The actual native image, whole pure carrier and original frames"),
                    StatementSource.FromAuthor(Disp(nativeGeometryStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("H lifts the actual Psi into Hermitian matrices, with no change of map or original carrier. Its full positive trace-one base is the image of the entire original base. The finite native matrix-rank-one decomposition property is equivalent to the original rho property by the normalization theorem. A PSD matrix of native rank one has exactly one nonzero eigenvalue. Its spectral expansion is that positive eigenvalue times a native eigenvector outer product; scaling the vector by its real square root gives a nonzero native outer product equal to the original matrix. The existing rankOne_real_smul identity is reused at its original public declaration. Under the finite decomposition property, this actual Hermitian image is ROG and its full pure carrier is the image of all original extreme points. Every original pure point extends at any prescribed index to a native orthonormal frame. The original states corresponding to all frame entries are pure, include the prescribed original point, and sum to the same h. Every such pure matrix is bounded by the identity. When the native dimension exceeds one, the original vector (h-p)/(n-1) belongs to the original base and H carries it to (I-H(p))/(n-1). The complement branch makes no assertion with a zero denominator."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-effect-geometry"),
                    DeclarationHandle.Create(Owner + "OriginalEffectGeometry"),
                    H("Compact original intervals and attained confirming comparisons"),
                    StatementSource.FromAuthor(Disp(effectGeometryStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The full original algebraic dual is embedded faithfully as its functions V to R with the pointwise product topology; coeFn is this canonical inclusion. The proper interval is compact in this topology. For every original p with u(p)=1, its entire confirmer set is compact and nonempty, and evaluation at every original x attains its minimum. The minimum equals the infimum of all actual confirming readings. For x in the original cone, that minimum is zero exactly when some original confirmer has zero reading. Every original linear functional is retained, with no finite-catalog or ambient-effect restriction. A generating cone writes every vector as a difference of two original cone vectors. Properness therefore bounds each pointwise reading in a compact real interval. Linearity and all proper inequalities define a closed subset of the product of those intervals. Tychonoff compactness gives the whole interval, intersection with the closed confirming equation gives compact confirmer sets, and the original unit u supplies their nonemptiness. The continuous evaluation map attains its minimum. Nonnegative readings on cone vectors give the zero equivalence. This proof does not require a prespecified minimizer, a PD dual representative or matrix full support."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("native-ambient-dimensions"),
                    DeclarationHandle.Create(Owner + "NativeAmbientDimensions"), H("Native ambient dimensions and trace codimension"),
                    StatementSource.FromAuthor(Disp(dimensionsStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every natural n, including zero, native real symmetric matrices have real dimension n(n+1)/2 and native complex Hermitian matrices have real dimension n squared. For every real linear subspace L in either native ambient space, its real dimension plus that of its trace orthogonal complement equals the corresponding ambient dimension. Real symmetric coordinates are real functions on unordered pairs of indices. The pinned Sym2 cardinality supplies their count. The complex formula directly reuses BipartiteSectorDecomposition.hermitian_space_finrank through the exact HermitianMat/selfAdjoint equivalence. The normalization theorem consumes these formulas at its actual positive native support dimension."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("native-original-congruence"),
                    DeclarationHandle.Create(Owner + "NativeCongruence"), H("The same ambient congruence and inverse annihilator transport"),
                    StatementSource.FromAuthor(Disp(congruenceStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("H and J lift the actual compressed sigma and normalized Psi into native Hermitian matrices. E is the invertible real linear ambient map A to S A S; its inverse is A to S inverse A S inverse. It maps every H(v) to J(v), so the whole image subspaces correspond and their real trace codimensions agree. Cyclicity of trace makes E self adjoint for the real trace inner product. Thus the reading of any ambient coefficient A on Psi(v) equals the reading of E(A) on sigma(v). In particular an annihilator of the Psi image is transported by E to an annihilator of the sigma image; an annihilator of the sigma image is transported by E inverse in the opposite direction. No ambient coefficient is passed through the inverse of the original-space embedding."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-unit-normalization"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_normalization"),
                    H("Actual original-unit normalization on the entire original carrier"),
                    StatementSource.FromAuthor(Disp(normalizationStatement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Use the very same compressed original mass-n point h supplied by inverse-trace stationarity. Its unique determinant maximum and principal inverse square root S define the real-linear map Psi(v) = S sigma(v) S on every original vector. Cyclicity of trace and S squared = sigma(h) inverse give trace Psi(v) = u(v), while S sigma(h) S = I makes the identity an actual member of this same image. Invertibility of S reconstructs sigma and then the original rho from every Psi(v); hence Psi is faithful. Congruence preserves Hermitian symmetry, the exact entire PSD cone section and native matrix rank. The image of the entire original unit-one base is exactly the positive trace-one part of this same linear image. No ambient dual lift is inverted and no normalized-section hypothesis is introduced. For each original cone element, finite decompositions into original native rank-one positive matrices correspond under the same Psi, retaining each original summand. Thus the entire ROG property transports in both directions. If the original base is a singleton and the cone is ROG, an actual rank-one summand of the full-support point is a positive multiple of that point. Its compressed matrix is positive definite and has rank n, forcing n = 1. The equivalence e from the original space onto the range of this same Psi carries the entire base and all its extreme points to the positive trace-one base in that range. It preserves convexity and every extreme subset, for arbitrary ambient subsets. It consequently carries the entire intersection of convex extreme subsets containing any prescribed set onto the corresponding intersection. This includes the entire minimal faces of both the original cone and its base. Its contravariant dual d(f) = f composed with e inverse carries the entire proper interval and each full confirmer set bijectively. For every original p and x, the sets of attainable confirming readings agree exactly, so their lower envelopes agree and d maps all minimizers onto all minimizers. In particular every actual zero confirmer transports in both directions, even when different zero conditions initially have different confirmers. Only elements of the actual image are passed to e inverse. When n is one, the original base and its entire extreme-point set are both the singleton containing the same h. Generation and strict positivity show every cone vector is its original mass times h. Thus every original effect is t times u with t in the closed unit interval, the only confirmer of h is u, and its entire exclusion set is empty. No division by n minus one occurs."))),
                    DescribeRole.Theorem),
                Paragraph(Text("For a concrete native real or complex application, take V = R, C = the nonnegative ray, u(x) = 2x and rho(x) = diag(x, 0). This representation is faithful and its entire PSD section is exactly C. The original base is the compact singleton {1/2}. The ambient matrix rho(1) is singular and its trace is one, whereas u(1) is two. Thus neither ambient full support nor an original trace unit is present. The native common support nevertheless has dimension one. The construction has h = 1/2 and Psi(x) = [2x] in the one-dimensional support, as its trace identity determines its only entry. It returns the entire original base and pure carrier {1/2}, confirmer {u}, empty exclusion set, and every proper effect t u for 0 <= t <= 1. The same native argument applies over R and C without replacing complex rank by real rank.")),
                Paragraph(Text("The actual Hermitian image and native matrix-rank-one bridge reuse SectionROGFrame.whole_pure_carrier and rog_frame. They return all original pure points, native frames summing to the same original h, and the same-h original complement for n greater than one. At the same support dimension, the native real and complex ambient dimensions are n(n+1)/2 and n squared, respectively. The actual compressed sigma and normalized Psi images have equal real trace codimension. The same ambient congruence A to S A S is trace self adjoint; it takes coefficients and annihilators of the normalized image to those of the compressed image, and its inverse returns them. These ambient coefficient maps are distinct from the inverse of the original-space embedding. The full original proper interval and every original confirmer set are compact under the faithful pointwise realization of all linear functionals; the original unit supplies nonemptiness. Every original confirming comparison attains its infimum, and on the cone its minimum is zero exactly when an actual original confirmer reads zero. The dimension-one singleton-base, entire effect interval and empty-exclusion return, and the converse from a singleton ROG base to support dimension one, are included. Classification and physical realization are not inferred. The linear-algebra, compact-extremum, polynomial-derivative and functional-calculus tools are standard; no literature priority is claimed.")))));
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
