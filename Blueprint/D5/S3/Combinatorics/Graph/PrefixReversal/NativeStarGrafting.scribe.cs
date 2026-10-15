using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeStarGraftingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual retained b-edge at one complete contact circle allows a whole deletion star to be grafted onto a Hamilton cycle.",
        H("Actual One-Contact Native E Grafting"),
        Blocks(
            Paragraph(Text(
                "Configurations are permutations of Fin(m+1), and a, b, c reverse the first m+1, m, "
                + "m-1 positions. SupplierStar(z) is the independently defined deletion star of the last "
                + "label of z, with the remaining tuple circle fixed up to whole reversal. GraftDomain(U,z) "
                + "is U union SupplierStar(z), and domainGraph(D) is the actual three-generator Cayley "
                + "graph induced on D. OldVertices(U) and UnionVertices(U,z) denote the corresponding "
                + "subtypes. liftOld(z,u) includes an old vertex into that union. The contact and all gap "
                + "circles are specified independently of the chosen paths. configurationEdges(w) maps "
                + "the actual typed edge list of w through the subtype value map. OldUncut(w,x,y,e) "
                + "means e occurs in that old list and differs from the actual contact {x.val,y.val}. "
                + "NewUncut(z,e) means e is a NativeCircleEdge in a nonzero gap and differs from its "
                + "literal b cut. ESeam(z,e) means e is {z_i*b,z_i*b*c} for an actual gap i.")),
            Describe.Lean(DescribeId.Create("native-one-contact-graft"),
                DeclarationHandle.Create(Prefix + "native_one_contact_graft"),
                H("The Actual E Ring Enlarges the Cycle and Retains Every Uncut Old Edge"),
                StatementSource.FromAuthor(GraftFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume m is at least three, w is an actual Hamilton cycle on an independent old "
                        + "domain U, x and y are old vertices with y=x*b, and their actual undirected edge "
                        + "occurs in w. Assume also that U meets SupplierStar(x) exactly in the complete "
                        + "circle Circle(x). Then there is an actual Hamilton cycle q on their full union, "
                        + "based at the configuration x. Every old edge other than {x,y} occurs in q. "
                        + "In each nonzero supplier gap, every native a/b edge other than that gap's "
                        + "actual b cut occurs in q. For every supplier gap i, the actual c edge from "
                        + "z_i*b to z_i*b*c also occurs in q, including the final return to gap zero. "
                        + "For every arbitrary undirected configuration edge e, membership in "
                        + "configurationEdges(q) is equivalent to OldUncut(w,x,y,e), NewUncut(x,e), "
                        + "or ESeam(x,e). Thus the full edge set contains exactly these three classes. "
                        + "The retained edges and new seams belong to this same constructed "
                        + "cycle, including old c edges; the theorem does not choose unrelated witnesses.")),
                    Paragraph(Text(
                        "Open the supplied old cycle at its actual contact edge, rotate and reverse as "
                        + "needed, and use the resulting complete Hamilton path from x to y as gap zero. "
                        + "At each other gap z_i=x*(b*c)^i, use the existing complete native b-complement "
                        + "from z_i to z_i*b. Lift these actual walks to the union's induced graph. "
                        + "The independent star coordinate partition exhausts all added vertices. "
                        + "Its gap circles are disjoint, and the one-contact assumption excludes every "
                        + "nonzero gap from the old domain. Thus the full piece supports are disjoint "
                        + "and contain every union vertex exactly once.")),
                    Paragraph(Text(
                        "Each consecutive pair is joined by the actual generator c, since "
                        + "z_i*b*c=z_(i+1). The previously proved complete E trace earns (b*c)^m=1, "
                        + "so the final c edge returns to gap zero. PathRingSplicing constructs a genuine "
                        + "Hamilton cycle from these actual full paths and real connections. Opening the "
                        + "old cycle removes exactly its contact edge. The native complement inventory "
                        + "retains every other a/b edge in a new circle, and injective induced edge maps "
                        + "and the exact spliced edge list carry both inventories into q. Adjacent "
                        + "indexed pieces place every interior seam into that literal edge list. "
                        + "The final piece is identified from the list's actual last element, and "
                        + "(b*c)^m=1 identifies the initial closing edge as the final supplier seam. Exact opening "
                        + "and complete native complement equivalences characterize every piece edge. "
                        + "An exhaustive classification of the literal chainEdges list shows that any "
                        + "remaining edge is one of the consecutive c seams. The closing first edge "
                        + "is the last E seam. These are both directions of the complete edge inventory."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The contact intersection and occurrence of the old b edge are explicit mathematical "
                + "hypotheses. Concrete core and supplier families must earn them before applying "
                + "this theorem. This result supplies an actual reusable enlargement step for all "
                + "m at least three; full second-layer coverage, actual marked-path recombination, "
                + "and the all-size recursive Hamiltonicity theorem remain separate obligations.")))));

    private static Formula GraftFormula()
    {
        Formula m = F.Id("m"), u = F.Id("U"), x = F.Id("x"), y = F.Id("y");
        Formula w = F.Id("w"), q = F.Id("q"), start = F.Id("start"), i = F.Id("i");
        Formula conf = Call("Configuration", m), old = Call("OldVertices", u);
        Formula z = Call("val", x), union = Call("UnionVertices", u, z);
        Formula edge(Formula a, Formula b) => Call("Sym2", a, b);
        Formula val(Formula a) => Call("val", a);
        Formula cut = edge(x, y), b = Call("b", m), c = Call("c", m);
        Formula contact = All("t", conf, Iff(
            And(Call("member", F.Id("t"), u), Call("SupplierStar", z, F.Id("t"))),
            Call("Circle", z, F.Id("t"))));
        Formula oldEdge = edge(F.Id("u"), F.Id("v"));
        Formula oldInventory = All("u", old, All("v", old, Implies(
            And(Member(oldEdge, Call("edges", w)), Not(Eq(oldEdge, cut))),
            Member(edge(Call("liftOld", z, F.Id("u")), Call("liftOld", z, F.Id("v"))),
                Call("edges", q)))));
        Formula gap = Call("gapAnchor", z, i), g = F.Id("g");
        Formula newEdge = edge(val(F.Id("u")), val(F.Id("v")));
        Formula newPremises = And(Call("Circle", gap, val(F.Id("u"))),
            And(Or(Eq(g, Call("a", m)), Eq(g, b)),
                And(Eq(val(F.Id("v")), Call("mul", val(F.Id("u")), g)),
                    Not(Eq(newEdge, edge(gap, Call("mul", gap, b)))))));
        Formula newInventory = All("i", Call("Fin", m), Implies(Not(Eq(val(i), D(0))),
            All("u", union, All("v", union, All("g", conf, Implies(newPremises,
                Member(edge(F.Id("u"), F.Id("v")), Call("edges", q))))))));
        Formula seamInventory = All("i", Call("Fin", m), Some("u", union, Some("v", union,
            And(Eq(val(F.Id("u")), Call("mul", gap, b)),
                And(Eq(val(F.Id("v")), Call("mul", val(F.Id("u")), c)),
                    Member(edge(F.Id("u"), F.Id("v")), Call("edges", q)))))));
        Formula rawEdge = F.Id("e");
        Formula fullInventory = All("e", Call("Sym2Type", conf), Iff(
            Member(rawEdge, Call("configurationEdges", q)),
            Or(Call("OldUncut", w, x, y, rawEdge),
                Or(Call("NewUncut", z, rawEdge), Call("ESeam", z, rawEdge)))));
        Formula cycle = Some("start", union, And(Eq(val(start), z),
            Some("q", Call("Walk", Call("domainGraph", Call("GraftDomain", u, z)), start, start),
                And(Call("IsHamiltonianCycle", q),
                    And(oldInventory, And(newInventory, And(seamInventory, fullInventory)))))));
        Formula hypotheses = And(Call("IsHamiltonianCycle", w),
            And(Eq(val(y), Call("mul", z, b)), And(Member(cut, Call("edges", w)), contact)));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("U", Call("Predicate", conf), All("base", old, All("x", old, All("y", old,
                All("w", Call("Walk", Call("domainGraph", u), F.Id("base"), F.Id("base")),
                    Implies(hypotheses, cycle)))))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
