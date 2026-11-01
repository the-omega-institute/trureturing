using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MobiusLadderSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rung coordinates give a graph isomorphism to the actual antipodal circulant at every size.", H("Native Mobius ladders and their complete spectra"), Blocks(
            Paragraph(Text("Write M(m) for the circulant on ZMod(2(m+2)) with jumps 1 and m+2. Both orientations of each jump are used and loops are excluded. The explicit coordinate (i,b) maps to i+(m+2)b. This is a bijection of the actual vertex types; it sends the rung flip to the antipodal jump and twisted forward transport to addition by one.")),
            Node("mobiusIso", "The native graph correspondence",
                All("m",C("Nat"),C("GraphIso",C("graph",C("closing",I("m"),D(1))),C("mobius",I("m")))),
                "The map preserves each of the three kinds of adjacency in both directions. At the closing rung it changes the binary label, exactly accounting for wraparound in the cyclic vertex set. Injectivity and looplessness handle the four-vertex boundary."),
            Node("mobius_spectrum", "Necessity and attainability",
                All("m",C("Nat"),All("k",C("Nat"),Iff(C("mem",I("k"),C("spectrum",C("mobius",I("m")))),And(Le(C("add",I("m"),D(2)),C("mul",D(2),I("k"))),And(Le(I("k"),C("add",I("m"),D(2))),C("Odd",I("k"))))))),
                "The graph isomorphism transports actual maximal independent Finsets and preserves their cardinalities. The complete binary closing spectrum then gives every odd cardinality in the stated interval and rules out every other cardinality.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
