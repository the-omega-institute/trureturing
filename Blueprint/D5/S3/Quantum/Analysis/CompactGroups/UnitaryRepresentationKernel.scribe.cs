using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.CompactGroups;

internal sealed class UnitaryRepresentationKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/CompactGroups/UnitaryRepresentationKernel.";
    private static LibraryNoteRef PeterWeyl => LibraryNoteRef.Create("D5/L/LieTheory/peterweyl1927vollstaendigkeit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every neighbourhood of the identity of a compact topological group contains the kernel of a continuous homomorphism into a unitary group of finite degree.",
        H("Small Kernels of Finite-Dimensional Unitary Representations of Compact Groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-representation-kernel-subset"),
                DeclarationHandle.Create(Prefix + "exists_unitaryRep_ker_subset"),
                H("A unitary representation with kernel inside a given neighbourhood"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(PeterWeyl),
                Blocks(
                    Paragraph(Text("Let G be a compact topological group; no separation axiom is assumed. Let U be a subset of G that is a neighbourhood of the identity 1. Then there are a natural number n and a continuous group homomorphism r from G into the group U(n) of unitary n x n complex matrices, written unitaryGroup(Fin(n), C), such that every g in G with r(g) = 1 lies in U. In other words, the kernel of r is contained in U. In a compact group with the T0 separation property points are closed, so every g other than 1 has a neighbourhood of 1 that does not contain g, and the statement yields a continuous finite-dimensional unitary representation that moves g; this is the separation form of the theorem of Peter and Weyl.")),
                    Paragraph(Text("Fix a Haar measure on G and the left regular representation of G on the square-integrable functions, in which g acts by sending f to the function whose value at x is f(g^(-1) x). This action preserves the norm and is continuous in g for each fixed f. Choose a neighbourhood V of 1 such that v w^(-1) lies in the interior of U for all v and w in V, and a continuous function phi that is nonzero at 1, vanishes outside V and has nonzero integral of phi squared. The integral operator T with kernel phi(x^(-1) y) maps the square-integrable functions compactly into the continuous functions on G, by the compactness of integral operators with a continuous kernel, and it commutes with the left regular representation by left invariance of the Haar measure. For g outside the interior of U the continuous function T(phi) takes the nonzero value given by the integral of phi squared at 1 and the value 0 at g, so translation by g moves T(phi).")),
                    Paragraph(Text("The operator S = T T*, where T* is the adjoint of T, is compact, self-adjoint and commutes with the representation. Its eigenspaces span a dense subspace, so a continuous operator that fixes every eigenspace of S with nonzero eigenvalue fixes the closure of the range of S, which contains the range of T. Hence for each c outside the interior of U some eigenspace of S with nonzero eigenvalue contains a vector moved by c, and then by every point of a neighbourhood of c. Eigenspaces of a compact operator with nonzero eigenvalue are finite-dimensional, and they are invariant under the representation. The complement of the interior of U is compact, so finitely many such eigenspaces suffice; their sum W is finite-dimensional and invariant, and the matrix of the representation on W in an orthonormal basis of W is the required homomorphism r. If r(g) = 1 then g fixes W and hence lies in the interior of U.")),
                    Paragraph(Text("Compactness of G cannot be dropped. In the group of affine maps x to a x + b of the real line with a positive, every continuous finite-dimensional unitary representation is trivial on all translations x to x + b, so no such kernel is contained in the neighbourhood of the identity formed by the maps with |b| < 1."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);

    private static Formula KernelFormula()
    {
        Formula g = F.Id("G"), u = F.Id("U"), n = F.Id("n"), r = F.Id("r"), x = F.Id("g");
        Formula unitary = Call("unitaryGroup", Call("Fin", n), Complexes);
        Formula small = ForAll("g", g,
            Implies(Equal(At(r, x), D(1)), Rel(x, FormulaRelationOperator.MemberOf, u)));
        Formula conclusion = Exists("n", Naturals,
            Exists("r", Call("ContinuousMonoidHom", g, unitary), small));
        return Disp(ForAll("G", TypeStar, Seq(
            Instance(Call("Group", g)),
            Instance(Call("TopologicalSpace", g)),
            Instance(Call("IsTopologicalGroup", g)),
            Instance(Call("CompactSpace", g)),
            ForAll("U", Call("Set", g),
                Implies(Rel(u, FormulaRelationOperator.MemberOf, Call("nhds", D(1))), conclusion)))));
    }
}
