using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class NonradicalLineRetractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026nonradical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A retraction onto lines and pairwise totally isotropic subspaces in every binary dimension.",
        H("Nonradical lines preserve the full orthogonality graph"),
        Blocks(
            Describe.Lean(DescribeId.Create("retained-vertices"),
                DeclarationHandle.Create(Prefix + "Retained"), H("The retained vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let F=ZMod 2, V(n)=Fin n -> F, and B be the existing standard coordinate pairing. "
                    + "Vertex(n) is the existing subtype of all nonzero submodules of V(n), including top. "
                    + "Retained(n,U) means finrank F U=1 or B(u,v)=0 for every u,v in U. "
                    + "The isotropic condition is pairwise; vanishing of B(u,u) alone is insufficient. "
                    + "A line can satisfy both branches."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("retained-graph"),
                DeclarationHandle.Create(Prefix + "retainedGraph"), H("The induced graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Write G(n) for NikandishClique.orthogonalityGraph n and S(n) for retainedGraph n. "
                    + "S(n) is G(n) induced on the actual subtype T(n) of retained vertices. "
                    + "Both graphs have distinct orthogonal endpoints as their adjacency relation. "
                    + "Write val for the inclusion T(n) -> Vertex(n), and space(U) for its submodule."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonradical-line-retraction"),
                DeclarationHandle.Create(Prefix + "result"), H("The complete contained retraction"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural dimension n there is a graph homomorphism r:G(n)->S(n) "
                        + "fixing every vertex of T(n), with space(r(U)) contained in space(U). "
                        + "Whenever val(r(U)) differs from U, its image has dimension one and is not "
                        + "contained in the right orthogonal of space(U). More precisely, its image "
                        + "is F span v for a nonzero v in U and some w in U has B(v,w) nonzero. "
                        + "The formula abbreviates finrank F by dim and uses B(n) on V(n).")),
                    Paragraph(Text(
                        "A vertex outside T(n) is not totally isotropic, so two vectors v,w in it "
                        + "have B(v,w) nonzero. The span of v is a nonzero line contained in that "
                        + "vertex. Symmetry converts B(v,w) nonzero to failure of membership in "
                        + "the right orthogonal. Choose such a line for each vertex outside T(n), "
                        + "and keep the vertices of T(n) fixed. No condition on B(v,v) is imposed.")),
                    Paragraph(Text(
                        "Containment sends orthogonal sources to orthogonal images. If an edge's "
                        + "images were equal and either endpoint moved, their common image would "
                        + "lie in the other endpoint and hence in the moved source's orthogonal, "
                        + "contradicting nonradicality. If neither endpoint moved, equality would "
                        + "contradict the original edge's distinctness. Thus r preserves actual edges.")),
                    Paragraph(Text(
                        "For any palette type alpha, a Coloring alpha on S(n) pulls back by "
                        + "Coloring.comap r. A Coloring alpha on G(n) restricts by "
                        + "Coloring.comap of (SimpleGraph.Embedding.induce).toHom. Hence "
                        + "Nonempty (G(n).Coloring alpha) is equivalent to "
                        + "Nonempty (S(n).Coloring alpha), including empty palettes. Applying "
                        + "chromaticNumber_mono_of_hom in both directions and antisymmetry gives "
                        + "equality of their Nat-infinity chromatic numbers. Colorable.of_hom "
                        + "is the corresponding consequence for palettes Fin k; it is not the "
                        + "arbitrary-palette predicate.")),
                    Paragraph(Text(
                        "At n=0 the original carrier is empty. At n=1 every vertex is the "
                        + "one-dimensional whole space and is retained. Top is included when "
                        + "nonzero (n>=1). In dimension two the vector (1,1) is self-isotropic "
                        + "but pairs nontrivially with (1,0), so its isotropic line is a permitted "
                        + "nonradical image of top. No finite cutoff or exact finite coloring "
                        + "number is asserted."))), DescribeRole.Theorem)), []));

    private static Formula ResultFormula()
    {
        var n = F.Id("n"); var r = F.Id("r"); var u = F.Id("U");
        var v = F.Id("v"); var w = F.Id("w");
        var image = Call("space", Call("apply", r, u));
        var source = Call("space", u);
        var fixedVertices = All("U", Call("T", n),
            Eq(Call("apply", r, Call("val", u)), u));
        var containment = All("U", Call("Vertex", n), Subset(image, source));
        var vectors = Exists("v", Call("V", n), And(In(v, source), And(Ne(v, F.D(0)),
            And(Eq(image, Call("span", F.Id("F"), v)), Exists("w", Call("V", n),
                And(In(w, source), Ne(Call("pair", Call("B", n), v, w), F.D(0))))))));
        var moved = All("U", Call("Vertex", n), Implies(
            Ne(Call("val", Call("apply", r, u)), u),
            And(Eq(Call("dim", image), F.D(1)), And(new Formula.Not(
                Subset(image, Call("orthogonal", Call("B", n), source))), vectors))));
        return F.Disp(All("n", F.Id("Nat"), Exists("r",
            Call("GraphHom", Call("G", n), Call("S", n)),
            And(fixedVertices, And(containment, moved)))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { F.Id(name), F.Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i != 0) items.Add(F.Comma);
            items.Add(arguments[i]);
        }
        items.Add(F.Close);
        return F.Seq([.. items]);
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Paren(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Paren(a), FormulaLogicOperator.And, Paren(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Paren(a), FormulaLogicOperator.Implies, Paren(b));
}
