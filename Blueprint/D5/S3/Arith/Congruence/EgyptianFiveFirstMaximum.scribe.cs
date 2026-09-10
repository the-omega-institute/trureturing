using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class EgyptianFiveFirstMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/batista2026a398581");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation of the first and maximal third denominators forces residue one modulo five.",
        H("First and maximum Egyptian fraction denominators"),
        Blocks(
            Describe.Lean(DescribeId.Create("a398581-solutions"),
                DeclarationHandle.Create(Prefix + "IsSolution"), H("Ordered integer solutions"),
                StatementSource.FromAuthor(SolutionFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("All four parameters are natural numbers. The defining "
                    + "equation is integral, and the three denominators are positive and strictly "
                    + "increasing."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a398581-first"),
                DeclarationHandle.Create(Prefix + "IsLexFirst"), H("The first solution"),
                StatementSource.FromAuthor(FirstFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The predicate includes being a solution and preceding "
                    + "every solution in the lexicographic order on all three coordinates. "
                    + "It does not assume that every parameter has a solution."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a398581-separation"),
                DeclarationHandle.Create(Prefix + "first_maximum_separation_mod_five"),
                H("Separation forces residue one"), StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Any competing solution with a larger third coordinate "
                    + "forces k to be one modulo five. A maximum-z solution supplies such a "
                    + "competitor whenever its third coordinate exceeds that of the first. "
                    + "The converse is not asserted.")),
                    Paragraph(Text("Write a=5x-k and b=kx. The positive integer gap ay-b "
                    + "bounds z. Before 5x=2k the bound decreases with x; after that point "
                    + "the strict order gives 25z <= 2k(2k+5). Explicit solutions at x=floor(k/5)+1 "
                    + "dominate all later x in residues zero, two, three and four. In the "
                    + "difficult residue-two branch, a=8 cannot have gap one, since this "
                    + "would force a square to be three modulo four. Small parameter branches "
                    + "use the same residual estimate."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula S(string a, string b, string c) =>
        Call("IsSolution", V("k"), V(a), V(b), V(c));
    private static Formula L() => Call("IsLexFirst", V("k"), V("x"), V("y"), V("z"));
    private static Formula SolutionFormula() => Disp(Seq(S("x", "y", "z"), Sp, Iff, Sp,
        D(0), Lt, V("x"), Lt, V("y"), Lt, V("z"), Sp, Land, Sp,
        D(5), V("x"), V("y"), V("z"), Eq, V("k"),
        P(Seq(V("y"), V("z"), Plus, V("x"), V("z"), Plus, V("x"), V("y")))));
    private static Formula FirstFormula()
    {
        var last = P(Seq(V("y"), Eq, V("v"), Sp, Land, Sp, V("z"), Le, Sp, V("w")));
        var middle = P(Seq(V("y"), Lt, V("v"), Sp, Lor, Sp, last));
        var equalFirst = P(Seq(V("x"), Eq, V("u"), Sp, Land, Sp, middle));
        var order = P(Seq(V("x"), Lt, V("u"), Sp, Lor, Sp, equalFirst));
        var all = P(Seq(Forall, Sp, V("u"), Comma, V("v"), Comma, V("w"), Comma, Sp,
            S("u", "v", "w"), Sp, Rightarrow, Sp, order));
        return Disp(Seq(L(), Sp, Iff, Sp, S("x", "y", "z"), Sp, Land, Sp, all));
    }
    private static Formula MainFormula() => Disp(Seq(
        L(), Sp, Land, Sp,
        P(Seq(Exists, Sp, V("u"), Comma, V("v"), Comma, V("w"), Comma, Sp,
            S("u", "v", "w"), Sp, Land, Sp, V("z"), Lt, V("w"))),
        Sp, Rightarrow, Sp, Call("mod", V("k"), D(5)), Eq, D(1)));
}
