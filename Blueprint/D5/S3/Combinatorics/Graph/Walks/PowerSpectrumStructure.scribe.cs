using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class PowerSpectrumStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph isomorphisms preserve distances and spectra, and complete powers have exact singleton spectra.", H("Native spectrum and metric transport"), Blocks(
            Paragraph(Text("All spectra use actual maximal independent vertex Finsets. Isomorphisms act on vertices, not merely on cardinality lists. Extended distance is used for arbitrary graphs; natural distance and diameter are obtained by conversion. A connected graph whose exponent reaches its diameter has a complete native power.")),
            Node("edist_iso", "Length-preserving metric transport",
                All("u",I("V"),All("v",I("V"),Eq(C("edist",I("H"),C("apply",I("e"),I("u")),C("apply",I("e"),I("v"))),C("edist",I("G"),I("u"),I("v"))))),
                "For every graph isomorphism e:G to H, map native finite walks through e and through its inverse. The two length bounds give equality even when vertices are unreachable. Natural distance and diameter are transported from the same equality."),
            Node("spectrum_top", "The attained spectrum of a nonempty complete graph",
                Eq(C("spectrum",C("completeGraph",I("V"))),C("singleton",D(1))),
                "Every maximal independent set is nonempty by domination. In a complete graph its vertices must all coincide, so its cardinality is one. Conversely, each singleton vertex set is independent and dominates all omitted vertices."),
            Node("power_eq_top_of_diam_le", "Every sufficiently large connected power is complete",
                Imp(And(C("Connected",I("G")),Le(C("diam",I("G")),I("d"))),Eq(C("power",I("G"),I("d")),C("completeGraph",I("V")))),
                "The native diameter bounds every pairwise distance in a finite connected graph. Consequently every two distinct vertices are adjacent in the stated power."),
            Node("wellCovered_iff_spectrum", "Uniformity is a subsingleton attained spectrum",
                Iff(C("WellCovered",I("G")),C("Subsingleton",C("spectrum",I("G")))),
                "The spectrum is defined by actual maximal independent Finsets. Equality of all their cardinalities is therefore equivalent to any two attained spectrum values being equal."),
            Node("spectrum_complement_triangleFree", "Triangle-free complements have exact spectrum two",
                Imp(And(C("TriangleFree",I("G")),All("u",I("V"),Ex("v",I("V"),C("Adj",I("G"),I("u"),I("v"))))),Eq(C("spectrum",C("complement",I("G"))),C("singleton",D(2)))),
                "Here V is nonempty and finite. A maximal independent set in the complement is a maximal clique in G. It cannot be a singleton because G has no isolated vertex, and it cannot have three distinct vertices because G is triangle-free. An existing finite maximum-independent-set supplier gives attainment.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
