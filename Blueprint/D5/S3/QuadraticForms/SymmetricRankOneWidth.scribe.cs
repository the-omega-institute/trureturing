using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SymmetricRankOneWidthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/SymmetricRankOneWidth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one coupling is bounded by the node width, with an exact equality criterion at a root of width greater than one.",
        H("Width saturation of symmetric block couplings"),
        Blocks(
            Paragraph(Text("Take a finite family of finite-dimensional real symmetric child blocks A(i) and a direction u in their Euclidean product. Let L be the set of nonleaves, w(i) the child widths, k(i) the child nullities, and k the nullity of the rank-one coupling of the block sum. The node width W is the maximum of one and the sum of w over L.")),
            Paragraph(Text("Leaf nullities are zero. A nonleaf nullity is at most its width, and equality for a nonleaf gives a kernel vector pairing nontrivially with its component of u. These hypotheses are the numerical and state inputs from cotree induction.")),
            Paragraph(Text("In the distance-spectrum application, the direction is the all-ones vector and its pairing is the coordinate sum. The root rule addresses equality in the distance multiplicity bound from Manna, Mandal and Tura, The Spectral Theory of Cographs, Theorem 6.4 and Open Problem 14.2(ii), arXiv:2611.06981v1.")),
            Paragraph(Text("The graph decomposition uses Seinsche's theorem in SimpleGraph.IsP4Free.not_preconnected_or_compl, the Apache-2.0 Lean Pool adaptation by Juan Pablo Traverso Gianini. The node widths use the vicinal chain-cover number, defined by inclusion of the open neighborhood of one vertex in the closed neighborhood of another.")),
            Entry("update_block_width", "The width bound and saturation state",
                Seq(V("k"), Sp, Leq, Sp, V("W"), Sp, Land, Sp, Open, V("k"), Eq, V("W"), Sp, Rightarrow, Sp, Call("Flag", V("U"), V("u")), Close), DescribeRole.Theorem,
                "For any nonzero real coupling t, k is bounded by W and equality gives a nonzero kernel pairing. When W > 1, equality holds exactly when L is a singleton {i}, k(i) + 1 = w(i), every block has scalar response g(j), and 1 + t times the sum of g(j) is zero. A flagged child lowers the summed nullity by one. In the scalar branch every nonleaf has a positive deficit, and resonance adds just one to the sum."),
            Entry("update_block_root_iff", "The one-nonleaf root criterion",
                Seq(V("k"), Eq, V("W"), Sp, Iff, Sp, Exists, Sp, V("i"), Comma, Sp, V("L"), Eq, OpenBrace, V("i"), CloseBrace, Sp, Land, Sp, D(0), Sp, Lt, Sp, Ell, Sp, Land, Sp, Call("k", V("i")), Plus, D(1), Eq, Call("w", V("i")), Sp, Land, Sp, Open, Exists, Sp, V("g"), Comma, Sp, Call("Response", Call("A", V("i")), Call("u", V("i")), V("g")), Sp, Land, Sp, D(1), Plus, V("g"), Minus, Seq(Frac, Grp(Ell), Grp(V("x"), Plus, D(1))), Eq, D(0), Close), DescribeRole.Theorem,
                "Use coupling one, at least two children, W > 1, and a common real shift x. Each leaf has nullity zero and response −1/(x + 1), and the nonleaf hypotheses are as above. Here ell is the number of leaves. Having only one nonleaf makes ell positive, and summing all child responses gives g − ell/(x + 1). In the distance application the shift is eligible when it differs from −1 and −2."))));

    private static DocumentBlock Entry(string name, string title, Formula statement,
        DescribeRole role, string explanation) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);

}
