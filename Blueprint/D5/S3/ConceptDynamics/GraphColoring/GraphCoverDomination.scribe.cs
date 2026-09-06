using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring.GraphDominationFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class GraphCoverDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.";
    private static readonly LibraryNoteRef Prior = LibraryNoteRef.Create("D5/L/neumann2009on");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite regular simple graph has a positive-fold cover dominated by one section.",
        H("Regular Graph Covers and Domination"),
        Blocks(
            Describe.Lean(DescribeId.Create("cover-definition"),
                DeclarationHandle.Create(Prefix + "IsCover"), H("Covering projection and fold"),
                StatementSource.FromAuthor(CoverDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here N_H(x) is the open neighborhood, and card is Nat.card. "
                    + "The map is onto, locally bijective, and has a constant fiber size. "
                    + "SimpleGraph supplies symmetry and excludes loops. No connectedness of G is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-cover-small-domination"),
                DeclarationHandle.Create(Prefix + "regular_cover_small_domination"), H("A cover dominated by stars"),
                StatementSource.FromAuthor(RegularCover()), AssessedProvenance.FromRepo(Prior),
                Blocks(Paragraph(Text("Gamma is the minimum size of a dominating set: every vertex belongs "
                    + "to it or has a neighbor in it. The definitions and minimum lemmas are a scoped "
                    + "licensed source port, identified in the Lean file. For each vertex choose a bijection "
                    + "between its neighbors and Fin d. The matching across an edge pairs each endpoint star "
                    + "with the opposite endpoint port; reverse transport is inverse transport. The stars dominate. "
                    + "Here pr1 denotes Prod.fst and card(V) equals Fintype.card V for a finite type. "
                    + "The port bijections are constructed from regularity, not assumed as an extra hypothesis. "
                    + "Existence of some finite cover admitting a perfect code already follows from "
                    + "the classical common-cover theorem; the present explicit construction is proof engineering."))),
                DescribeRole.Theorem))));

    private static Formula CoverDefinition()
    {
        Formula v = F.Id("v"), x = F.Id("x"), p = F.Id("p"), k = F.Id("k");
        Formula g = F.Id("G"), f = F.Id("F"), V = F.Id("V"), W = F.Id("W");
        Formula local = Seq(Forall, Sp, Typed(x, W), Comma,
            Call("BijOn", p, Call("neighborSet", g, x), Call("neighborSet", f, Call("p", x))));
        Formula fibers = Seq(Forall, Sp, Typed(v, V), Comma,
            Call("card", SetBuilder(Typed(x, W), EqTo(Call("p", x), v))), Eq, k);
        return Display(Seq(Forall, Sp, Typed(V, Type()), Comma, Typed(W, Type()), Comma,
            Typed(f, Call("SimpleGraph", V)), Comma, Typed(g, Call("SimpleGraph", W)), Comma,
            Typed(p, Seq(W, Sp, To, Sp, V)), Comma, Typed(k, Nat()), Comma, RowBreak, Grp(),
            Call("IsCover", g, f, p, k), Iff,
            And(Call("Surjective", p), local, fibers)));
    }

    private static Formula RegularCover()
    {
        Formula V = F.Id("V"), f = F.Id("F"), g = F.Id("G"), d = F.Id("d");
        return Display(Seq(Forall, Sp, Typed(V, Type()), Comma, Typed(F.Id("fv"), Call("Fintype", V)), Comma,
            Typed(f, Call("SimpleGraph", V)), Comma, Typed(F.Id("dec"), Call("DecidableRel", Call("Adj", f))), Comma,
            Typed(d, Nat()), Comma, Call("IsRegularOfDegree", f, d), Sp, Rightarrow, Sp, RowBreak, Grp(),
            Exists, Sp, Typed(g, Call("SimpleGraph", Seq(V, Sp, Times, Sp, Call("Option", Call("Fin", d))))), Comma,
            And(Call("IsCover", g, f, Seq(Operatorname, Grp(F.Id("pr1"))), PlusOne(d)),
                Seq(Gamma(g), Sp, Le, Sp, Call("card", V)))));
    }
}

internal static class GraphDominationFormula
{
    internal static Formula Sup(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    internal static Formula SetBuilder(Formula binder, Formula predicate) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, predicate, CloseBrace);
    internal static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));
    internal static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    internal static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    internal static Formula Typed(Formula x, Formula type) => Seq(x, Colon, Sp, type);
    internal static Formula PlusOne(Formula x) => Seq(Open, x, Plus, D(1), Close);
    internal static Formula EqTo(Formula x, Formula y) => Seq(x, Eq, y);
    internal static Formula And(params Formula[] clauses)
    {
        List<Formula> items = [];
        for (int i = 0; i < clauses.Length; i++)
        {
            if (i > 0) { items.Add(Sp); items.Add(Land); items.Add(Sp); }
            items.Add(Seq(Open, clauses[i], Close));
        }
        return Seq([.. items]);
    }
    internal static Formula Gamma(Formula g) => Call("dominationNumber", g);
    internal static Formula Display(Formula body) => Disp(Seq(Begin, Grp(F.Id("gathered")), body, End, Grp(F.Id("gathered"))));
}
