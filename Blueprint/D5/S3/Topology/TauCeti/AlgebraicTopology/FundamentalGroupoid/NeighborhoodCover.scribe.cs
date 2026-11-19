using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid;

internal sealed class NeighborhoodCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict functors on an arbitrary neighborhood cover glue uniquely, and the ordinary finite-intersection open Cech cocone is a colimit in groupoids.",
        H("Neighborhood-cover gluing and the ordinary Cech colimit"),
        Blocks(
            Describe.Lean(DescribeId.Create("exists-unique-extension"),
                DeclarationHandle.Create(Prefix + "existsUnique_extension"),
                H("Strict extension from an arbitrary neighborhood cover"),
                StatementSource.FromAuthor(F.Disp(ExtensionStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/tauceti2026vankampenneighborhoodcover")),
                Blocks(Paragraph(Text(
                    "For every topological space X, every index type I and every family U of subsets of X whose members are neighborhoods pointwise, and every target category D, compatible functors on the subtype fundamental groupoids of the U(i) have a unique strict extension to the fundamental groupoid of X. The cover members need not be open, intersections may be empty, and no connectedness, finiteness, basepoint or nonempty-intersection premise is added."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cech-colimit"),
                DeclarationHandle.Create(Prefix + "isColimitCechCocone"),
                H("The ordinary finite-intersection Cech cocone"),
                StatementSource.FromAuthor(F.Disp(CechStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/tauceti2026vankampenneighborhoodcover")),
                Blocks(Paragraph(Text(
                    "For an arbitrary open cover, the diagram is indexed by nonempty finite subsets ordered by reverse inclusion. Its objects are the fundamental groupoids of the corresponding intersections, with geometric empty intersections retained by the diagram. The displayed cocone is an ordinary IsColimit in Grpd; no pseudocolimit or natural-isomorphism replacement is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cech-diagram"),
                DeclarationHandle.Create(Prefix + "cechDiagram"),
                H("Fundamental-groupoid Cech diagram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/tauceti2026vankampenneighborhoodcover")), Blocks(Paragraph(Text(
                    "cechDiagram is the fundamental-groupoid image of the finite-intersection open diagram."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cech-cocone"),
                DeclarationHandle.Create(Prefix + "cechCocone"),
                H("Canonical inclusion cocone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/tauceti2026vankampenneighborhoodcover")), Blocks(Paragraph(Text(
                    "cechCocone maps every intersection fundamental groupoid to the full-space fundamental groupoid through its subtype inclusion."))),
                DescribeRole.Definition))));

    private static Formula ExtensionStatement()
    {
        var X = V("X"); var I = V("I"); var D = V("D"); var U = V("U");
        var i = V("i"); var j = V("j"); var x = V("x"); var G = V("G");
        var setX = Call("Set", X);
        var fund = (Formula a) => Call("FundamentalGroupoid", a);
        var functor = (Formula a, Formula b) => Call("Functor", a, b);
        var inclusion = (Formula a, Formula b) => Call("inclusion", a, b);
        var map = (Formula f) => Call("map", f);
        var comp = (Formula a, Formula b) => Call("comp", a, b);
        var neighborhood = Call("nhds", x);
        var hU = All("x", X, Ex("i", I, Member(Call("U", i), neighborhood)));
        var left = comp(map(inclusion(Call("inter", Call("U", i), Call("U", j)), Call("U", i))), Call("F", i));
        var right = comp(map(inclusion(Call("inter", Call("U", i), Call("U", j)), Call("U", j))), Call("F", j));
        var hF = All("i", I, All("j", I, Eq(left, right)));
        var restriction = comp(map(Call("subtypeVal", Call("U", i))), G);
        var conclusion = All("i", I, Eq(restriction, Call("F", i)));
        var unique = Seq(Exists, Bang, Sp, Parenthesized(Seq(G, Colon, Sp,
            functor(fund(X), D))), Comma, Sp, conclusion);
        var body = Implies(Parenthesized(hU), Implies(Parenthesized(hF), unique));
        var localFamilyType = Parenthesized(All("i", I, functor(fund(Call("U", i)), D)));
        body = All("F", localFamilyType, body);
        body = All("U", new Formula.TypeArrow(I, setX), body);
        body = All("D", Call("Type", V("w")), Bracket(Call("Category", V("z"), D)), body);
        body = All("z", V("UniverseLevel"), body);
        body = All("I", Call("Type", V("v")), body);
        body = All("X", Call("Type", V("u")), Bracket(Call("TopologicalSpace", X)), body);
        return body;
    }

    private static Formula CechStatement()
    {
        var X = V("X"); var I = V("I"); var U = V("U");
        var body = Implies(Call("IsOpenCover", U), Call("IsColimit", Call("cechCocone", U)));
        body = All("U", new Formula.TypeArrow(I, Call("Opens", X)), body);
        body = All("I", Call("Type", V("u")), body);
        return All("X", Call("TopCat", V("v")), body);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [..args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula instance, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, instance, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Bracket(Formula x) => Seq(OpenBracket, x, CloseBracket, Sp);
}
