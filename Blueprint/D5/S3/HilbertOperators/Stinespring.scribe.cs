using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class StinespringDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/atlas2026stinespring");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completely positive maps from arbitrary unital complex C*-algebras admit a common Hilbert-space representation and bounded compression.",
        H("Stinespring dilation for arbitrary completely positive maps"),
        Blocks(Describe.Lean(DescribeId.Create("stinespring-dilation"),
            DeclarationHandle.Create("D5/S3/HilbertOperators/Stinespring.stinespring_dilation"),
            H("Generic Stinespring dilation"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Fix any universe u. A and H are types in that SAME universe. C denotes the complex numbers, CPLinearMap(C,A,B(H)) denotes CompletelyPositiveMap A (H ->L[C] H), and B(E) denotes the bounded complex-linear endomorphisms of E. CStarAlgebra A is the unital complex C*-algebra structure. The separate PartialOrder A and StarOrderedRing A instances give the compatible positive cone. H is a complete complex inner product space.")),
                Paragraph(Text("There exist a type K in Type u, its normed additive group, complex inner product and completeness structures, a unital complex star-algebra homomorphism pi from A to B(K), and a bounded complex-linear map V from H to K. For these SAME K, structures, pi and V, every a in A and every x in H satisfy phi(a)(x) = adjoint(V)(pi(a)(V(x))). StarAlgHom(C,A,B(K)) includes preservation of the unit, multiplication, addition, complex scalars and star. CLM(C,H,K) denotes continuous complex-linear maps, equivalently bounded linear maps in this setting. Adjoint(V) is the Hilbert-space adjoint from K to H.")),
                Paragraph(Text("On finitely supported functions f,g from A to H, form the sesquilinear expression obtained by summing inner(f(a), phi(star(a)*b)(g(b))) over their supports. Complete positivity makes its diagonal nonnegative: positive operator matrices have nonnegative quadratic forms, and the matrix with entries star(a)*b is positive. The resulting seminormed inner product space has a separated Hilbert completion K. Left multiplication by c in A has norm bounded by norm(c), so it extends to K. These extensions preserve multiplication, the unit and star and define pi.")),
                Paragraph(Text("The map V sends x to the completion class of the finitely supported function concentrated at the algebra unit with value x. Its norm is at most sqrt(norm(phi(1)))*norm(x). Evaluating the sesquilinear form on these vectors gives inner(V(y), pi(a)(V(x))) = inner(y, phi(a)(x)); adjointness and separation by inner products give the stated identity.")),
                Paragraph(Text("The theorem applies without finite dimension or separability. Complete positivity of phi is required; phi need not preserve the unit or a trace. V is asserted bounded, with no isometry conclusion. No minimality, uniqueness, dimension bound, recovery map or tensor-product realization is asserted. Finite Kraus models are special settings of operator dilation, while this statement permits arbitrary unital C*-algebras and arbitrary complex Hilbert spaces at the stated universe scope."))),
            DescribeRole.Theorem))));

    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] xs)
    {
        var a = new List<Formula> { Operatorname, Grp(V(n)), Open };
        for (int i = 0; i < xs.Length; i++) { if (i > 0) a.AddRange([Comma, Sp]); a.Add(xs[i]); }
        a.Add(Close); return Seq([.. a]);
    }
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Inst(string n, Formula b, params Formula[] xs) => Seq(OpenBracket, Call(n, xs), CloseBracket, Sp, b);
    private static Formula Statement()
    {
        Formula compression = Call("Apply", Call("Adjoint", V("V")),
            Call("Apply", Call("pi", V("a")), Call("V", V("x"))));
        Formula result = All("a", V("A"), All("x", V("H"), Seq(
            Call("Apply", Call("phi", V("a")), V("x")), Sp, Eq, Sp, compression)));
        result = Some("V", Call("CLM", V("C"), V("H"), V("K")), result);
        result = Some("pi", Call("StarAlgHom", V("C"), V("A"), Call("B", V("K"))), result);
        result = Some("completeK", Call("CompleteSpace", V("K")), result);
        result = Some("innerK", Call("InnerProductSpace", V("C"), V("K")), result);
        result = Some("normedK", Call("NormedAddCommGroup", V("K")), result);
        result = Some("K", Call("Type", V("u")), result);
        result = All("phi", Call("CPLinearMap", V("C"), V("A"), Call("B", V("H"))), result);
        result = Inst("CompleteSpace", result, V("H"));
        result = Inst("InnerProductSpace", result, V("C"), V("H"));
        result = Inst("NormedAddCommGroup", result, V("H"));
        result = Inst("StarOrderedRing", result, V("A"));
        result = Inst("PartialOrder", result, V("A"));
        result = Inst("CStarAlgebra", result, V("A"));
        return All("u", V("Universe"), All("A", Call("Type", V("u")),
            All("H", Call("Type", V("u")), result)));
    }
}
