using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class PentagonalPrismSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Chinese-remainder coordinates identify the square complement with a ten-cycle.", H("The square of the pentagonal prism"), Blocks(
            Paragraph(Text("P5 is the native Cartesian graph cycleGraph(5) box-product K2. Map a ten-cycle vertex j to (2j mod 5,j mod 2). The Chinese remainder equivalence, followed by multiplication by the unit 2 modulo 5, supplies a bijection of the actual vertices. The cycle and product distance suppliers check adjacency in both directions.")),
            Node("pentagon_square_complement_iso", "The actual complement-cycle correspondence",
                C("GraphIso",C("cycleGraph",D(1,0)),C("complement",C("power",C("prism",D(2)),D(2)))),
                "Two prism vertices fail to be adjacent in its square exactly when their base cycle separation is two and their binary labels differ. Under the displayed coordinates these are precisely consecutive vertices of the ten-cycle. A triangle-free graph without isolated vertices has two-vertex maximal cliques, so the general complement-spectrum supplier proves the middle power directly in the all-positive-power classification. Pham and Vu, arXiv 2610.09300v1 Example 3.8, already give this well-covered-powers example; no novelty is claimed.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
}
