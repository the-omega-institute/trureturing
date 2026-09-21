using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ProperCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/Separable/ProperCut.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/fu2019two");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual classical 2413/3142 avoidance implies a nonempty proper direct or skew cut.",
        H("Classical avoidance and a proper cut"),
        Blocks(
            Paragraph(Text(
                "This is the known classical bridge recorded "
                + "in Proposition 2.1 of the cited source, with an internal graph proof. "
                + "It does not settle the real-rootedness assertion in Conjecture 5.2.")),
            Node("pattern2413", "The literal pattern 2413", DescribeRole.Definition,
                PatternFormula("pattern2413", 1, 3, 0, 2),
                "This permutation of Fin(4) has values 1, 3, 0, 2 at positions 0, 1, 2, 3. "
                + "The bracket notation lists its values in increasing position order."),
            Node("pattern3142", "The literal pattern 3142", DescribeRole.Definition,
                PatternFormula("pattern3142", 2, 0, 3, 1),
                "This permutation of Fin(4) has values 2, 0, 3, 1 at positions 0, 1, 2, 3."),
            Node("avoidance_proper_cut", "A nonempty proper direct or skew cut", DescribeRole.Theorem,
                ProperCutFormula(),
                "Here Fin(n) consists of the positions 0 through n-1, and Perm(n) is the set "
                + "of permutations of Fin(n). Contains(q,p) means that some strictly increasing "
                + "choice of positions in p has exactly the relative value order of q. "
                + "For every natural n at least two and every permutation p avoiding both "
                + "literal patterns, there is a natural m with 1 <= m < n such that either "
                + "p(i) < p(j) for every pair of positions i < m <= j, or p(j) < p(i) "
                + "for every such pair. Both parts of the cut are nonempty, and all value "
                + "inequalities are strict. An induced four-vertex path in the inversion "
                + "graph supplies one of the two forbidden patterns. A maximal disconnected "
                + "induced subset proves that the graph or its complement is disconnected. "
                + "A boundary dart makes the root component order-convex, and its least omitted "
                + "position supplies the cut."),
            Paragraph(Text(
                "Real-rootedness of the actual-avoider descent polynomials remains unproved here. "
                + "The source's tree bijection "
                + "requires the greatest valid cut, standardization, preservation of actual "
                + "avoidance, and descent correspondence. Those conclusions and the "
                + "real-rootedness proof are not supplied by this existence theorem.")))));

    private static DocumentBlock Node(
        string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula PatternFormula(string name, byte a, byte b, byte c, byte d) =>
        Disp(Seq(Operatorname, Grp(F.Id(name)), Eq,
            OpenBracket, D(a), Comma, D(b), Comma, D(c), Comma, D(d), CloseBracket));

    private static Formula ProperCutFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("p"), InMacro, Call("Perm", F.Id("n")), Comma, Sp,
        Open, D(2), Le, Sp, F.Id("n"), Land, Sp,
        Neg, Sp, Call("Contains", F.Id("pattern2413"), F.Id("p")), Land, Sp,
        Neg, Sp, Call("Contains", F.Id("pattern3142"), F.Id("p")), Close, Rightarrow, Sp,
        Exists, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(1), Le, Sp, F.Id("m"), Land, Sp, F.Id("m"), Lt, F.Id("n"), Land, Sp,
        Open, CutFormula("i", "j"), Lor, Sp, CutFormula("j", "i"), Close));

    private static Formula CutFormula(string smaller, string larger) => Seq(
        Open, Forall, Sp, F.Id("i"), Comma, F.Id("j"), InMacro,
        Call("Fin", F.Id("n")), Comma, Sp,
        Open, F.Id("i"), Lt, F.Id("m"), Land, Sp, F.Id("m"), Le, Sp, F.Id("j"), Close,
        Rightarrow, Sp, Call("p", F.Id(smaller)), Lt, Call("p", F.Id(larger)), Close);
}
