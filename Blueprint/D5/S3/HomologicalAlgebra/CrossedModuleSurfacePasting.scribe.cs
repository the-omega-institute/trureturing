using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class CrossedModuleSurfacePastingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.";

    private static Formula X => F.Id("X");
    private static Formula HGroup => F.Id("H");
    private static Formula GGroup => F.Id("G");
    private static Formula Shell => F.Id("T");
    private static Formula Q8Module => Named("q8CrossedModule");
    private static Formula One => D(1);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Peiffer interchange governs typed face pasting. A tetrahedral shell can have a nonidentity central obstruction.",
        H("Crossed-module surface pasting"),
        Blocks(
            Paragraph(Text("A crossed module consists of a group homomorphism μ from H to G and an action of G on H by automorphisms. Equivariance says that μ sends the action by p to conjugation by p. The Peiffer identity says that the action by μ(h) is conjugation by h.")),
            Law("ker_le_center", "The kernel is central", Kernel(),
                "If μ(h) is the identity, the Peiffer identity gives hkh⁻¹ = k for every k in H. Right multiplication by h gives commutativity with h."),
            Law("fake_flat_iff", "The face boundary equation", FakeFlatness(),
                "Right multiplication by the inverse source path gives the fake-flatness equation. Right multiplication by the source path recovers the boundary equation."),
            Paragraph(Text("Write v(h,k) for vertical pasting, with label kh, and m(h,k) for horizontal pasting, with label h times the action by the first source path on k. The letter ℓ denotes the label of a face. Equivariance gives the horizontal target path by carrying the second boundary through the first source path. The identity face i(X,p) has label 1 at both copies of path p.")),
            Law("vertical_laws", "Vertical identity and associativity", Vertical(),
                "Both identity laws follow from the unit in H. Associativity compares products of three labels in reverse traversal order."),
            Law("horizontal_laws", "Horizontal identity and associativity", Horizontal(),
                "Identity and associativity follow because the action is a homomorphism into automorphisms. Group associativity identifies the endpoint products of the two triple pastings."),
            Law("interchange", "Peiffer interchange", Interchange(),
                "For h from p to q, the relation q = μ(h)p gives (q acting on k')h = h(p acting on k'). Substitute this equality in the vertical paste of the two horizontal rows, and use multiplicativity of the action. The two results are faces with the same endpoints and the same label."),
            Paragraph(Text("The face on ijk runs from edge gain gᵢₖ to the product gᵢⱼgⱼₖ. The left paste uses face 013 followed by face 123 whiskered by edge 01. Its label A is the product of the action by g₀₁ on h₁₂₃ and h₀₁₃. The right paste uses face 023 followed by face 012 whiskered by edge 23. Its label B is h₀₁₂h₀₂₃. Both run from g₀₃ to g₀₁(g₁₂g₂₃). Write Ω for AB⁻¹.")),
            Law("obstruction_mem_ker", "The obstruction is in the kernel",
                Tetrahedral(Mem(Obstruction(Shell), Call("ker", X))),
                "Cancelling the common source in the two boundary equations gives μ(A) = μ(B). Applying μ to their ratio gives the identity."),
            Law("obstruction_mem_center", "The obstruction is central",
                Tetrahedral(Mem(Obstruction(Shell), Call("center", HGroup))),
                "Apply the central kernel property to the ratio."),
            Law("obstruction_eq_one_iff", "Triviality is equality of composite labels",
                Tetrahedral(Rel(Eqn(Obstruction(Shell), One), Leftrightarrow,
                    Eqn(Label(Call("left", Shell)), Label(Call("right", Shell))))),
                "Multiplying the ratio equation by B on the right gives A = B. Substituting A = B gives the identity ratio."),
            Law("q8_tetrahedron_nontrivial", "A quaternion shell with obstruction minus one",
                Quantify(Exists, "T", Call("Tetrahedron", Q8Module),
                    Rel(Eqn(Obstruction(Shell), Call("a", D(2))), Land,
                        Rel(Obstruction(Shell), Neq, One))),
                "Write a and x for the quaternion generators. The map to the Klein four group sends aⁱ to (0, i mod 2) and xaⁱ to (1, i mod 2). Conjugation descends to the quotient because its kernel consists of 1 and a², both central. On edges 01 and 12 use the images of a and x. Give every other edge gain 1. The faces 012, 013, 023 and 123 have labels xa, a, 1 and x. The resulting composites have labels ax = xa³ and xa. Their ratio is a², distinct from 1."),
            Law("result", "Facewise fake flatness permits a nontrivial shell",
                Seq(Neg, Sp, Parens(Quantify(Forall, "T", Call("Tetrahedron", Q8Module),
                    Eqn(Obstruction(Shell), One)))),
                "The four quaternion faces satisfy their boundary equations. The ratio of their composites is the central element a²."))));

    private static DocumentBlock Law(string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create("crossed-module-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parens(Formula body) => Seq(Open, body, Close);
    private static Formula Rel(Formula lhs, Formula relation, Formula rhs) =>
        Seq(lhs, Sp, relation, Sp, rhs);
    private static Formula Eqn(Formula lhs, Formula rhs) => Rel(lhs, Eq, rhs);
    private static Formula Mem(Formula term, Formula set) => Rel(term, InMacro, set);
    private static Formula Mul(Formula lhs, Formula rhs) => Rel(lhs, Cdot, rhs);
    private static Formula MuAt(Formula term) => Call("mu", X, term);
    private static Formula Obstruction(Formula term) => Call("Omega", term);
    private static Formula Label(Formula term) => Call("ell", term);
    private static Formula Identity(Formula path) => Call("i", X, path);
    private static Formula Vertically(Formula first, Formula second) => Call("v", first, second);
    private static Formula Horizontally(Formula first, Formula second) => Call("m", first, second);
    private static Formula Quantify(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Parens(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);

    private static Formula General(Formula body) => Quantify(Forall, "u", Named("Universe"),
        Quantify(Forall, "v", Named("Universe"), Quantify(Forall, "H", Call("Type", F.Id("u")),
            Quantify(Forall, "G", Call("Type", F.Id("v")), Seq(
                OpenBracket, Call("Group", HGroup), CloseBracket, Sp,
                OpenBracket, Call("Group", GGroup), CloseBracket, Comma, Sp,
                Quantify(Forall, "X", Call("CrossedModule", HGroup, GGroup), body))))));

    private static Formula Paths(Formula body, params string[] paths) =>
        paths.Reverse().Aggregate(body, (rest, path) => Quantify(Forall, path, GGroup, rest));

    private static Formula Cell(string name, string source, string target, Formula body) =>
        Quantify(Forall, name, Call("Face", X, F.Id(source), F.Id(target)), body);

    private static Formula Kernel() => General(Quantify(Forall, "h", HGroup, Rel(
        Mem(F.Id("h"), Call("ker", X)), Rightarrow, Mem(F.Id("h"), Call("center", HGroup)))));

    private static Formula FakeFlatness()
    {
        var h = F.Id("h");
        var p = F.Id("p");
        var q = F.Id("q");
        return General(Paths(Quantify(Forall, "h", HGroup, Rel(
            Eqn(Mul(MuAt(h), p), q), Leftrightarrow,
            Eqn(MuAt(h), Mul(q, Seq(p, Caret, Grp(Minus, One)))))), "p", "q"));
    }

    private static Formula Vertical()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var l = F.Id("l");
        var laws = Rel(Parens(Eqn(Vertically(Identity(F.Id("p")), h), h)), Land,
            Rel(Parens(Eqn(Vertically(h, Identity(F.Id("q"))), h)), Land,
                Eqn(Vertically(Vertically(h, k), l), Vertically(h, Vertically(k, l)))));
        return General(Paths(Cell("h", "p", "q", Cell("k", "q", "r", Cell("l", "r", "s", laws))),
            "p", "q", "r", "s"));
    }

    private static Formula Horizontal()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var l = F.Id("l");
        var laws = Rel(Parens(Eqn(Label(Horizontally(Identity(One), h)), Label(h))), Land,
            Rel(Parens(Eqn(Label(Horizontally(h, Identity(One))), Label(h))), Land,
                Eqn(Label(Horizontally(Horizontally(h, k), l)),
                    Label(Horizontally(h, Horizontally(k, l))))));
        return General(Paths(Cell("h", "p", "q", Cell("k", "a", "b", Cell("l", "c", "d", laws))),
            "p", "q", "a", "b", "c", "d"));
    }

    private static Formula Interchange()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var j = F.Id("j");
        var l = F.Id("l");
        var equality = Eqn(Vertically(Horizontally(h, k), Horizontally(j, l)),
            Horizontally(Vertically(h, j), Vertically(k, l)));
        return General(Paths(Cell("h", "p", "q", Cell("k", "a", "b",
            Cell("j", "q", "r", Cell("l", "b", "c", equality)))), "p", "q", "r", "a", "b", "c"));
    }

    private static Formula Tetrahedral(Formula body) =>
        General(Quantify(Forall, "T", Call("Tetrahedron", X), body));
}
