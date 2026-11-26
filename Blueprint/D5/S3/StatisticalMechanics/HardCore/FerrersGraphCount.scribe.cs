using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class FerrersGraphCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Zeros/tahoangnguyen2026ferrers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count independent sets of the Ferrers graph by their least selected row.",
        H("The Ferrers independence polynomial"),
        Blocks(
            Node("vertex", "Vertex", "Disjoint vertex sets", StatementSource.WithoutFormula(),
                "Rows and columns form the tagged disjoint sum of the two finite index sets.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graph", "graph", "Ferrers adjacency", StatementSource.WithoutFormula(),
                "With zero-based row and column indices, row i meets column j exactly when j is less than the length of row i. Edges only join the two parts.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polynomial", "independencePolynomial_ferrers", "Least-row enumeration",
                StatementSource.FromAuthor(Disp(Seq(Call("I", F.Id("G"), F.Id("X")), Eq,
                    Pow(Par(Seq(D(1), Plus, F.Id("X"))), F.Id("m")), Plus, F.Id("X"),
                    Sum, Underscore, Grp(F.Id("i")), Pow(Par(Seq(D(1), Plus, F.Id("X"))), Subscript("e", "i"))))),
                "The row lengths are nonincreasing. The sum ranges over the zero-based row indices and e_i is n − 1 − i + (m − λ_i), with natural subtraction. The first term counts column-only sets. If i is the least selected row, the later rows and the columns outside its neighborhood may be chosen freely.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("coefficients", "coeff_independencePolynomial_eq_card_indepSetFinset", "Coefficients count actual sets",
                StatementSource.FromAuthor(Disp(Seq(Coeff("k", Call("I", F.Id("G"), F.Id("X"))), Eq,
                    Vert, Call("indepSetFinset", F.Id("G"), F.Id("k")), Vert))),
                "For a finite simple graph G, selecting the degree-k monomials keeps precisely the Mathlib independent sets of size k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("empty", "card_indepSetFinset_ferrers_zero", "The empty independent set",
                StatementSource.FromAuthor(Disp(Seq(Vert, Call("indepSetFinset", F.Id("G"), D(0)), Vert, Eq, D(1)))),
                "The empty subset is the unique independent set of size zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("binomial", "card_indepSetFinset_ferrers_succ", "Independent sets of positive size",
                StatementSource.FromAuthor(Disp(Seq(Vert, Call("indepSetFinset", F.Id("G"), Seq(F.Id("k"), Plus, D(1))), Vert,
                    Eq, Call("choose", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Plus,
                    Sum, Underscore, Grp(F.Id("i")), Call("choose", Subscript("e", "i"), F.Id("k"))))),
                "The row lengths are nonincreasing. For each possible least row i, choose k additional vertices from the e_i free vertices. Column-only sets choose k + 1 columns.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string name, string title, StatementSource statement,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("ferrers-graph-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), statement, provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula content) => Seq(Open, content, Close);
    private static Formula Pow(Formula bas, Formula exponent) => Seq(bas, Caret, Grp(exponent));
    private static Formula Subscript(string symbol, string index) => Seq(F.Id(symbol), Underscore, Grp(F.Id(index)));
    private static Formula Coeff(string index, Formula polynomial) =>
        Seq(OpenBracket, Pow(F.Id("X"), F.Id(index)), CloseBracket, polynomial);
}
