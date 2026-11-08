using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RayPhaseRigidityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RayPhaseRigidity.";

    public DocumentDefinition Create()
    {
        Formula iota = F.Id("iota"), a = F.Id("A"), x = F.Id("x"),
            i = F.Id("i"), j = F.Id("j"), c = F.Id("c"), tests = F.Id("S"),
            p = F.Id("p"), q = F.Id("q");
        Formula vectors = Seq(iota, To, C);
        Formula matrices = Call("Matrix", iota, iota, C);
        Formula ray(Formula y) => Call("PreservesRay", a, y);
        Formula member(Formula y) => Seq(y, InMacro, Sp, tests);
        Formula apply(Formula f, Formula y) => Seq(f, Open, y, Close);
        Formula connected = Call("RaySupportConnected", tests);
        Formula edge = Seq(Open, p, Comma, q, Close, Mapsto, Sp,
            Ex("x", vectors, And(member(x),
                And(NeqF(apply(x, p), D(0)), NeqF(apply(x, q), D(0))))));
        Formula indexContext(Formula body) => All("iota", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", iota), CloseBracket, Sp, body));
        Formula context(Formula body) => indexContext(All("A", matrices, body));
        Formula predicateContext(Formula body) => All("iota", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", iota), CloseBracket, Sp, All("A", matrices, body)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A support-connected family of invariant rays determines a unitary global phase.",
            H("Connected ray tests and global phase"), Blocks(
                Paragraph(Text("Let iota be a finite decidable index type, possibly empty, let A be a complex matrix on iota, and let S be a set of complex vectors on iota. Ray preservation means that A x lies in the complex span of x. Support connectivity means that every pair of indices is linked by the reflexive-transitive closure of the relation that holds when some x in S is nonzero at both indices. If A is unitary, preserves the ray of single i 1 for every i, preserves the ray of every x in S, and S is support-connected, then there is c in C with norm(c) = 1 and A = c times the identity matrix. Sparse test supports are allowed; in the empty case c = 1. The statement makes no claim about CP maps, density supports, or computational semantics.")),
                Item("PreservesRay", "Invariance of a complex line",
                    predicateContext(All("x", vectors, IffF(ray(x),
                        Seq(Call("mulVec", a, x), InMacro, Sp, Call("span", C, SetOf(x)))))),
                    "The image of x lies in its complex span. At zero the condition is automatic. For a unitary and nonzero x the inclusion gives equality of rays.", true),
                Item("RaySupportConnected", "Connectivity through test supports",
                    All("iota", F.Id("Type"), All("S", Call("Set", vectors), IffF(connected,
                        All("i", iota, All("j", iota, Call("ReflTransGen", edge, i, j)))))),
                    "Two coordinates are adjacent when a test vector is nonzero at both. ReflTransGen is the reflexive transitive closure of this relation. Every pair of coordinates must be linked by a finite chain. Tests may have sparse supports; neither a full-support test nor a positive dimension is required.", true),
                Item("unitary_phase_of_connected_ray_tests", "Connected invariant ray tests force a global phase",
                    context(Imp(Seq(a, InMacro, Sp, Call("unitaryGroup", iota, C)),
                        Imp(All("i", iota, ray(Call("single", i, D(1)))),
                            All("S", Call("Set", vectors),
                                Imp(All("x", vectors, Imp(member(x), ray(x))),
                                    Imp(connected, Ex("c", C, And(Eqn(Norm(c), D(1)),
                                        Eqn(a, Seq(c, Cdot, Call("IdentityMatrix", iota))))))))))),
                    "Coordinate-ray invariance removes all off-diagonal entries. A test vector gives a common diagonal coefficient on every nonzero coordinate in its support. Induction along support chains propagates this equality to every pair of coordinates. Hence A = c I; unitarity gives conjugate(c) c = 1 and norm(c) = 1. In dimension zero choose c = 1. For one coordinate, reflexivity supplies connectivity even with no tests."),
                Paragraph(Text("Application to Proposition 7.6: equal subspace images under U and V imply that W = V adjoint times U preserves every ray. The coordinate rays and the all-ones ray satisfy the theorem's premises: the singleton family containing the all-ones vector connects every pair of coordinates in one step. Thus W = c I and U = c V, with norm(c) = 1. This uses at most cardinality(iota) + 1 ray tests. The statement concerns linear images of subspaces; density-support and CP-map semantics are outside its scope.")),
                Paragraph(Text("Reuse boundary: Mathlib's LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent supplies scalarity from all-vector collinearity. The repository's sparse_probe_coercivity bounds the scalar defect using one normalized full-support probe. The present theorem supplies propagation across a connected family even when every test has sparse support. No literature originality is claimed.")))));
    }

    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NeqF(Formula left, Formula right) => Seq(left, Neq, Sp, right);
    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula SetOf(Formula x) => Seq(OpenBrace, x, CloseBrace);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static DocumentBlock Item(string name, string title, Formula formula,
        string explanation, bool definition = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
