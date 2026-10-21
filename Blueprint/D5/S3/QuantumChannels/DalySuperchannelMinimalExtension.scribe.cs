using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class DalySuperchannelMinimalExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/daly2022axiomatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit quantum superchannel has reduced Choi rank four for every extension and a minimizing extension that is a midpoint of distinct extensions.",
        H("A non-extreme minimum-rank superchannel extension"), Blocks(
            Entry("channel-span", "SCPTP", "The span of quantum channels", SpanFormula(),
                "Definition 3.1, page 3: \"Given positive integers d, r ≥ 1 define SCPTP(d, r) := span{φ | φ : M_d → M_r is a CPTP map} ⊂ L(M_d, M_r). Also define S(d, r) ⊂ M_d(M_r) to be the set of block matrices (P_{i,j}) such that for all 1 ≤ i, j ≤ d, Tr(P_{i,i}) = Tr(P_{j,j}) and for i ≠ j Tr(P_{i,j}) = 0.\" The complex span is formed in MatrixMap, whose elements are complex-linear matrix maps. Complete positivity is MatrixMap.IsCompletelyPositive; trace preservation is stated for every input matrix. Fin n indices start at zero.", Literature()),
            Entry("tensor-bilinear", "kronBilin", "The bilinear tensor product of matrix maps", KronBilinFormula(),
                "Remark 3.3, page 4: \"A tensor product of linear maps gives a map on the tensor product of the spaces so there is an inclusion\". The bilinear map is LinearMap.mk₂ applied to MatrixMap.kron, with its additive and scalar laws. The displayed equality specifies its value on every pair of maps.", Literature()),
            Entry("tensor-lift", "kronLift", "The tensor-product lift", KronLiftFormula(),
                "Remark 3.3, page 4: \"A tensor product of linear maps gives a map on the tensor product of the spaces so there is an inclusion\". TensorProduct.lift applies the bilinear map kronBilin to arbitrary tensors, including sums of elementary tensors.", Literature()),
            Entry("qsc", "IsQSC", "Quantum superchannels on channel spans", QscFormula(),
                "Definition 3.4, page 5: \"Given two spaces of quantum channels SCPTP(d_i, r_i), i = 1, 2, a QSC is a linear map Γ : SCPTP(d_1, r_1) → SCPTP(d_2, r_2) which satisfies (1) if φ is CPTP then Γ(φ) is CPTP (2) given any other dimensions d_3, r_3 ∈ ℕ and the identity map id_{d_3,r_3} : SCPTP(d_3, r_3) → SCPTP(d_3, r_3) then Γ⊗id_{d_3,r_3} : SCPTP(d_1, r_1)⊗SCPTP(d_3, r_3) → SCPTP(d_2, r_2)⊗SCPTP(d_3, r_3) sends CP maps to CP maps.\" Subtype.val includes the span into the full map space, and TensorProduct.map includes both tensor factors. The second condition ranges over every auxiliary dimension and every tensor.", Literature()),
            Entry("full-superchannel", "IsQuantumSuperchannel", "Superchannels on full map spaces", SuperchannelFormula(),
                "Remark 3.7, page 6: \"a quantum superchannel is a linear map S : L(M_{d_1}, M_{r_1}) → L(M_{d_2}, M_{r_2}) which satisfies • CP preserving: S sends CP maps to CP maps • Completely CP preserving: For any d, r if id_{d,r} is the identity map acting on L(M_d, M_r) then S ⊗ id_{d,r} is CP preserving • TP preserving: S sends TP maps to TP maps\" All three clauses concern the full complex-linear map spaces; the last clause applies to every trace-preserving input, without a positivity hypothesis.", Literature()),
            Entry("extensions", "extensions", "The set of extensions", ExtensionsFormula(),
                "Theorem 3.8, page 6: \"Every QSC extends to a quantum superchannel.\" The set here consists of the full superchannels agreeing with Gamma on every element of SCPTP. Agreement is equality of matrix maps, after Subtype.val on both sides.", Literature()),
            Entry("choi", "choi", "The input-first Choi matrix", ChoiFormula(),
                "Section 2, page 3: \"Now any linear map is determined by its action on basis elements so for a linear L : M_d → M_r we get a vector space isomorphism from L(M_d, M_r) onto M_d(M_r) via L ↦ (L(E_{i,j})).\" The entry with row (i,k) and column (j,l) is the (k,l) entry of L applied to Matrix.single i j 1.", Literature()),
            Entry("choi-equivalence", "choiEquiv", "The Choi linear equivalence", ChoiEquivFormula(),
                "Section 2, page 3: \"Now any linear map is determined by its action on basis elements so for a linear L : M_d → M_r we get a vector space isomorphism from L(M_d, M_r) onto M_d(M_r) via L ↦ (L(E_{i,j})).\" The forward action applies L to each matrix unit. Its inverse maps X and Y to the matrix with entry ∑ i, ∑ j, Y i j * X (i,k) (j,l). Only the input carrier A requires Fintype and DecidableEq instances.", Literature()),
            Entry("induced", "induced", "The induced map on Choi matrices", InducedFormula(),
                "After Definition 3.4, page 5: \"If Γ is a QSC it induces a map Γ̃ : S(d_1, r_1) → S(d_2, r_2) via Γ̃ = R_2 ∘ Γ ∘ R_1^{−1}.\" For a full superchannel S the same composition acts on all block matrices. The displayed expression uses the forward and inverse Choi linear equivalences.", Literature()),
            Entry("rank", "e", "The reduced Choi rank", RankFormula(),
                "Section 4, page 10: \"The dimension e can be chosen to be the rank of Tr_{r_1} Tr_{r_2} C_{Γ̃}\" The permutation Equiv.prodProdProdComm changes ((d1,r1),(d2,r2)) to ((d1,d2),(r1,r2)); partialTraceRight traces out the latter pair, and Matrix.rank takes the complex rank.", Literature()),
            Entry("question", "claim", "The minimum-rank extremality question", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "Remark 4.1, page 11: \"The set of possible superchannel extensions of a QSC is a convex set. In the example given the extensions with minimal e are extreme points. A natural question to ask is whether it is generally true that the extensions which give minimal dimensions e are extreme points.\" The proposition quantifies over four positive dimensions, every QSC Gamma and every minimizing extension S. The comparison includes all extensions G, and extremePoints uses real scalars.", Literature()),
            Entry("refutation", "result", "A non-extreme minimizing extension", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "For dimensions 2,2,2,2, take the restriction of the map induced by F₀, where Fₛ(X) = X/2 + (I ⊗ TrA X)/8 + Tr(X)I/16 + s Tr((Z ⊗ I)X)(Z ⊗ I)/32 and Z = diag(1,−1). For −1 ≤ s ≤ 1 these maps give extensions with the same restriction. Their fixed off-diagonal coherence block is positive definite. Compressing any extension against a vector in the kernel of its reduced Choi matrix gives a positive semidefinite matrix of trace zero, contradicting that block's strict positivity. Thus every extension has e = 4. The extension at s = 0 is the midpoint of the distinct extensions at s = 1 and s = −1, so it minimizes e and is not extreme. The existence of an extreme minimizer is a separate question.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static AssessedProvenance Literature() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SpanFormula()
    {
        Formula d = V("d"), r = V("r"), phi = V("phi");
        return Disp(All("d", Nat(), All("r", Nat(), Equal(Call("SCPTP", d, r),
            Call(Q("Submodule", "span"), Complex(), SetOf("phi", Map(d, r), Cptp(phi, d)))))));
    }
    private static Formula KronBilinFormula() => Disp(Types(All("phi", GenericMap(V("A"), V("B")),
        All("psi", GenericMap(V("C"), V("D")), Equal(Call("kronBilin", V("phi"), V("psi")),
            Call(Q("MatrixMap", "kron"), V("phi"), V("psi"))))), true));
    private static Formula KronLiftFormula() => Disp(Types(Equal(
        Parenthesized(Seq(V("kronLift"), Colon, Sp, Linear(Tensor(GenericMap(V("A"), V("B")), GenericMap(V("C"), V("D"))),
            GenericMap(Pair(V("A"), V("C")), Pair(V("B"), V("D")))))),
        Call(Q("TensorProduct", "lift"), V("kronBilin"))), true));
    private static Formula QscFormula()
    {
        Formula gamma = V("Gamma"), phi = V("phi"), t = V("t");
        Formula first = All("phi", Span(V("d1"), V("r1")),
            Imp(Cptp(Val(phi), V("d1")), Cptp(Val(App(gamma, phi)), V("d2"))));
        Formula aux = Tensor(Span(V("d1"), V("r1")), Span(V("d3"), V("r3")));
        Formula input = Lift(Tmap(Subtype(V("d1"), V("r1")), Subtype(V("d3"), V("r3")), t));
        Formula output = Lift(Tmap(Subtype(V("d2"), V("r2")), Subtype(V("d3"), V("r3")), Tmap(gamma, Q("LinearMap", "id"), t)));
        Formula second = All("d3", Nat(), All("r3", Nat(), All("t", aux, Imp(Cp(input), Cp(output)))));
        return Disp(Dims(All("Gamma", SpanMap(), Equal(Call("IsQSC", gamma), And(first, second)))));
    }
    private static Formula SuperchannelFormula()
    {
        Formula s = V("S"), phi = V("phi"), t = V("t");
        Formula first = All("phi", Map(V("d1"), V("r1")), Imp(Cp(phi), Cp(App(s, phi))));
        Formula second = All("d", Nat(), All("r", Nat(), All("t", Tensor(Map(V("d1"), V("r1")), Map(V("d"), V("r"))),
            Imp(Cp(Lift(t)), Cp(Lift(Tmap(s, Q("LinearMap", "id"), t)))))));
        Formula third = All("phi", Map(V("d1"), V("r1")), Imp(Tp(phi, V("d1")), Tp(App(s, phi), V("d2"))));
        return Disp(Dims(All("S", SuperMap(), Equal(Call("IsQuantumSuperchannel", s), And(first, And(second, third))))));
    }
    private static Formula ExtensionsFormula()
    {
        Formula agreement = All("phi", Span(V("d1"), V("r1")),
            Equal(App(V("S"), Val(V("phi"))), Val(App(V("Gamma"), V("phi")))));
        Formula members = SetOf("S", SuperMap(), And(Call("IsQuantumSuperchannel", V("S")), agreement));
        return Disp(Dims(All("Gamma", SpanMap(), Equal(Call("extensions", V("Gamma")), members))));
    }
    private static Formula ChoiFormula()
    {
        Formula a = V("A"), b = V("B"), l = V("L");
        return Disp(All("A", Type(), All("B", Type(), Instance("DecidableEq", a,
            ChoiAction(Call("choi", l), a, b)))));
    }
    private static Formula ChoiAction(Formula forward, Formula a, Formula b)
    {
        Formula l = V("L"), i = V("i"), j = V("j"), k = V("k"), ell = V("l");
        return All("L", GenericMap(a, b), All("i", a, All("j", a, All("k", b, All("l", b,
            Equal(App(forward, Tuple(i, k), Tuple(j, ell)),
                App(l, Call(Q("Matrix", "single"), i, j, D(1)), k, ell)))))));
    }
    private static Formula ChoiEquivFormula()
    {
        Formula a = V("A"), b = V("B"), equivalence = Call("choiEquiv", a, b);
        Formula x = V("X"), y = V("Y"), i = V("i"), j = V("j"), k = V("k"), ell = V("l");
        Formula forward = ChoiAction(App(Member(equivalence, "toFun"), V("L")), a, b);
        Formula summand = Seq(App(y, i, j), Sp, Cdot, Sp, App(x, Tuple(i, k), Tuple(j, ell)));
        Formula inverse = All("X", Mat(Pair(a, b)), All("Y", Mat(a), All("k", b, All("l", b,
            Equal(App(Member(equivalence, "invFun"), x, y, k, ell),
                SumOver("i", a, SumOver("j", a, summand)))))));
        return Disp(All("A", Type(), All("B", Type(), Instance("Fintype", a, Instance("DecidableEq", a,
            And(forward, inverse))))));
    }
    private static Formula InducedFormula() => Disp(Dims(All("S", SuperMap(), Equal(Call("induced", V("S")),
        Compose(Member(Call("choiEquiv", Fin(V("d2")), Fin(V("r2"))), "toLinearMap"),
            Compose(V("S"), Member(Member(Call("choiEquiv", Fin(V("d1")), Fin(V("r1"))), "symm"), "toLinearMap")))))));
    private static Formula RankFormula()
    {
        Formula shuffle = Call(Q("Equiv", "prodProdProdComm"), Fin(V("d1")), Fin(V("r1")), Fin(V("d2")), Fin(V("r2")));
        Formula reindexed = App(Member(Call(Q("LiJiangPolarPairOptimalityRefutation", "inputFirstChoi"), Call("induced", V("S"))), "reindex"), shuffle, shuffle);
        return Disp(Dims(All("S", SuperMap(), Equal(Call("e", V("S")),
            Member(Call(Q("PartialTraceMutualInformation", "partialTraceRight"), reindexed), "rank")))));
    }
    private static Formula ClaimBody()
    {
        Formula s = V("S"), g = V("G"), gamma = V("Gamma"), exts = Call("extensions", gamma);
        Formula minimal = All("G", SuperMap(), Imp(In(g, exts), Le(Call("e", s), Call("e", g))));
        Formula extreme = App(Member(exts, "extremePoints"), Real());
        Formula body = All("Gamma", SpanMap(), Imp(Call("IsQSC", gamma), All("S", SuperMap(),
            Imp(In(s, exts), Imp(minimal, In(s, extreme))))));
        foreach (string name in new[] { "r2", "d2", "r1", "d1" }) body = Imp(Le(D(1), V(name)), body);
        return Dims(body);
    }
    private static Formula Types(Formula body, bool four)
    {
        if (four) body = All("C", Type(), All("D", Type(),
            Instance("Fintype", V("A"), Instance("DecidableEq", V("A"), Instance("Fintype", V("B"),
            Instance("Fintype", V("C"), Instance("DecidableEq", V("C"), Instance("Fintype", V("D"), body))))))));
        return All("A", Type(), All("B", Type(), body));
    }
    private static Formula Dims(Formula body) => All("d1", Nat(), All("r1", Nat(), All("d2", Nat(), All("r2", Nat(), body))));
    private static Formula Cptp(Formula phi, Formula d) => And(Cp(phi), Tp(phi, d));
    private static Formula Tp(Formula phi, Formula d) => All("X", Mat(Fin(d)), Equal(Trace(App(phi, V("X"))), Trace(V("X"))));
    private static Formula Cp(Formula phi) => Call(Q("MatrixMap", "IsCompletelyPositive"), phi);
    private static Formula Trace(Formula x) => Member(x, "trace");
    private static Formula Lift(Formula t) => Call("kronLift", t);
    private static Formula Tmap(Formula a, Formula b, Formula t) => Call(Q("TensorProduct", "map"), a, b, t);
    private static Formula Subtype(Formula d, Formula r) => Member(Span(d, r), "subtype");
    private static Formula Span(Formula d, Formula r) => Call("SCPTP", d, r);
    private static Formula SpanMap() => Linear(Span(V("d1"), V("r1")), Span(V("d2"), V("r2")));
    private static Formula SuperMap() => Linear(Map(V("d1"), V("r1")), Map(V("d2"), V("r2")));
    private static Formula Map(Formula d, Formula r) => GenericMap(Fin(d), Fin(r));
    private static Formula GenericMap(Formula a, Formula b) => Call("MatrixMap", a, b, Complex());
    private static Formula Mat(Formula a) => Call("Matrix", a, a, Complex());
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Linear(Formula a, Formula b) => Seq(Parenthesized(a), Sp, new Formula.Subscript(To, Complex()), Sp, Parenthesized(b));
    private static Formula Tensor(Formula a, Formula b) => Call("TensorProduct", Complex(), a, b);
    private static Formula Compose(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Circ, Sp, Parenthesized(b));
    private static Formula Type() => V("Type");
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Member(Formula x, string name) => Seq(Parenthesized(x), Dot, V(name));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string f, params Formula[] args) => Call(V(f), args);
    private static Formula Call(Formula f, params Formula[] args) => App(f, args);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Tuple(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Pair(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string n, Formula t, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(n), Colon, Sp, t)), Comma, Sp, body);
    private static Formula Instance(string name, Formula type, Formula body) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);
    private static Formula SetOf(string n, Formula t, Formula body) => Seq(OpenBrace, V(n), Colon, Sp, t, Sp, Vert, Sp, body, CloseBrace);
}
