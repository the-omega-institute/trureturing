using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class NeighborhoodIndependenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Fibers/BipartiteBlockade/NeighborhoodIndependence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent blocking neighborhoods retain distinct correlation coordinates.",
        H("Blocking Coordinates Beyond Single Occupations"),
        Blocks(Describe.Lean(
            DescribeId.Create("blocking-independent-mod-singletons"),
            DeclarationHandle.Create(Prefix + "blocking_independent_mod_singletons"),
            H("Independence modulo constants and single occupations"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a simple graph and let F be a finite family of distinct "
                    + "independent vertex sets, each containing at least two vertices. For an "
                    + "independent configuration S, the blocking function associated with N "
                    + "is one precisely when N and S are disjoint. No nonzero linear "
                    + "combination of these functions can equal a constant plus a linear "
                    + "combination of the single-site occupations on every independent S.")),
                Paragraph(Text(
                    "The separating calculation uses all subsets S of a chosen independent "
                    + "set N, with coefficient minus one to the cardinality of S. Its sum "
                    + "against a blocking function for M is one when N is contained in M "
                    + "and zero otherwise. The same signed sum kills the constant and every "
                    + "single occupation because N has at least two elements. Choosing N "
                    + "of largest cardinality among the nonzero coefficients isolates one "
                    + "coefficient and gives a contradiction.")),
                Paragraph(Text(
                    "For a bipartite graph every open neighborhood is an independent set. "
                    + "Thus the result applies to the distinct open neighborhoods of size "
                    + "at least two. It establishes the independence of their diagonal "
                    + "correlation coordinates modulo the known means; it does not by itself "
                    + "construct density matrices or determine an acceleration fiber."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, Sp, C("Type"), Comma, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, Sp, C("SimpleGraph", V("V")), Comma, Sp,
        V("F"), Colon, Sp, C("Finset", C("Finset", V("V"))), Comma, Sp,
        V("c"), Colon, Sp, C("Finset", V("V")), Rightarrow, Sp, C("Real"), Comma, Sp,
        V("q"), Colon, Sp, C("Real"), Comma, Sp,
        V("s"), Colon, Sp, V("V"), Rightarrow, Sp, C("Real"), Comma, Sp,
        Open, Forall, Sp, V("N"), InMacro, Sp, V("F"), Comma, Sp,
        C("independent", V("G"), V("N")), Sp, Land, Sp,
        D(2), Le, Sp, C("card", V("N")), Close, Rightarrow, Sp,
        Open, Forall, Sp, V("S"), Comma, Sp,
        C("independent", V("G"), V("S")), Rightarrow, Sp,
        C("sum", V("F"), V("N"),
            Seq(C("c", V("N")), C("disjointIndicator", V("N"), V("S")))),
        Sp, Eq, Sp, V("q"), Plus, C("sum", V("S"), V("v"), C("s", V("v"))),
        Close, Rightarrow, Sp,
        Forall, Sp, V("N"), InMacro, Sp, V("F"), Comma, Sp,
        C("c", V("N")), Sp, Eq, Sp, D(0), Dot));
}
