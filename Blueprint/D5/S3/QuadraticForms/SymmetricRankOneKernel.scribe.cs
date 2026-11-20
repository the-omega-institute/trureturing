using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SymmetricRankOneKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/SymmetricRankOneKernel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real symmetric rank-one update has three exact transitions for its kernel and scalar response.",
        H("Symmetric rank-one kernel transitions"),
        Blocks(
            Paragraph(Text("Let B be a symmetric linear map on a real inner-product space E and e a direction in E. Write U for the map x ↦ Bx + t ⟨e,x⟩e, and write k(B) for the real finrank of its kernel. A flagged state has a kernel vector whose pairing with e is nonzero. A scalar response g means that By = e has a solution and that every solution has pairing g with e.")),
            Paragraph(Text("Finite dimensionality is required for the exhaustive state split and the two nullity changes. The symmetry law and the nonresonant kernel identity hold on an arbitrary real inner-product space.")),
            Entry("HasNonzeroPairing", "Nonzero pairing in the kernel",
                Seq(Call("Flag", V("B"), V("e")), Sp, Iff, Sp, Exists, Sp, V("z"), Sp, InMacro, Sp, Call("ker", V("B")), Comma, Sp, Pair("z"), Sp, Neq, Sp, D(0)), DescribeRole.Definition,
                "The witness lies in the actual kernel and pairs nontrivially with the given direction."),
            Entry("ScalarResponse", "Scalar response to the update direction",
                Seq(Call("Response", V("B"), V("e"), V("g")), Sp, Iff, Sp, Open, Exists, Sp, V("y"), Comma, Sp, Call("B", V("y")), Eq, V("e"), Close, Sp, Land, Sp, Open, Forall, Sp, V("y"), Comma, Sp, Call("B", V("y")), Eq, V("e"), Sp, Rightarrow, Sp, Pair("y"), Eq, V("g"), Close), DescribeRole.Definition,
                "The existence clause prevents a vacuous response for an inconsistent right-hand side."),
            Entry("update", "Symmetric rank-one update",
                Eq(Call("U", V("x")), Seq(Call("B", V("x")), Plus, V("t"), Pair("x"), V("e"))), DescribeRole.Definition,
                "The update direction appears in both the linear functional and the displaced vector."),
            Entry("update_symmetric", "Symmetry of the update",
                Seq(Call("Symmetric", V("B")), Sp, Rightarrow, Sp, Call("Symmetric", V("U"))), DescribeRole.Theorem,
                "The quadratic contribution to the bilinear pairing is symmetric in its two arguments."),
            Entry("solvable_iff_no_nonzero_pairing", "Solvability and vanishing kernel pairings",
                Seq(Open, Exists, Sp, V("y"), Comma, Sp, Call("B", V("y")), Eq, V("e"), Close, Sp, Iff, Sp, Neg, Call("Flag", V("B"), V("e"))), DescribeRole.Theorem,
                "For finite-dimensional E, the range of B is the orthogonal complement of its kernel."),
            Entry("nonzero_pairing_or_unique_scalar", "The exhaustive kernel and response states",
                Seq(Call("Flag", V("B"), V("e")), Sp, Lor, Sp, Open, Exists, D(1), Sp, V("g"), Comma, Sp, Call("Response", V("B"), V("e"), V("g")), Close), DescribeRole.Theorem,
                "In finite dimension, solvability supplies a response whenever the flag is absent. Two solutions differ by a kernel vector and have the same pairing."),
            Entry("update_of_nonzero_pairing", "Nullity loss from a flagged kernel",
                Seq(Call("k", V("U")), Plus, D(1), Eq, Call("k", V("B")), Sp, Land, Sp, Call("Response", V("U"), V("e"), Seq(Frac, Grp(D(1)), Grp(V("t"))))), DescribeRole.Theorem,
                "In finite dimension, assume the flag for B and t ≠ 0. Pairing the new kernel equation with the flagged vector cuts out the kernel of one nonzero functional on ker B. Scaling that vector supplies a solution of Uy = e with response 1/t."),
            Entry("update_of_resonance", "Nullity gain at scalar resonance",
                Seq(Call("k", V("U")), Eq, Call("k", V("B")), Plus, D(1), Sp, Land, Sp, Call("Flag", V("U"), V("e"))), DescribeRole.Theorem,
                "In finite dimension, assume response g for B and 1 + tg = 0. A solution of By = e lies in the new kernel with nonzero pairing g. It adds one direction to the old kernel."),
            Entry("update_of_nonresonance", "Kernel preservation away from resonance",
                Seq(Call("ker", V("U")), Eq, Call("ker", V("B")), Sp, Land, Sp, Call("Response", V("U"), V("e"), Seq(Frac, Grp(V("g")), Grp(D(1), Plus, V("t"), V("g"))))), DescribeRole.Theorem,
                "Assume response g for B and 1 + tg ≠ 0. The kernel equation forces zero pairing, and scaling a solution of By = e by the reciprocal of the resonance factor gives the new response."),
            Entry("blockDiagonal", "Block-diagonal linear map",
                Eq(Call("D", V("x"), V("i")), Call("A", V("i"), Call("x", V("i")))), DescribeRole.Definition,
                "On the Euclidean product, the map acts on each coordinate by that coordinate's block."),
            Entry("blockDiagonal_states", "Kernel and response states of a block sum",
                Seq(Call("k", V("D")), Eq, Sum, Sp, Call("k", Call("A", V("i"))), Sp, Land, Sp, Open, Call("Flag", V("D"), V("u")), Sp, Iff, Sp, Exists, Sp, V("i"), Comma, Sp, Call("Flag", Call("A", V("i")), Call("u", V("i"))), Close), DescribeRole.Theorem,
                "For a finite family of finite-dimensional symmetric blocks A with direction u in the Euclidean product, D is symmetric, its nullity is the sum of the child nullities, and its flag is equivalent to the existence of a child flag. If every child has scalar response g(i) at direction u(i), then D has response equal to their sum. The kernel is a product and the inner product is a sum of coordinate pairings."))));

    private static DocumentBlock Entry(string name, string title, Formula statement,
        DescribeRole role, string explanation) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Pair(string x) => Seq(Langle, V("e"), Comma, V(x), Rangle);
}
