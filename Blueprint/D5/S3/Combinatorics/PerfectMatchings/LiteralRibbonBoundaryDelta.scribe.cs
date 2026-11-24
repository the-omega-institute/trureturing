using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class LiteralRibbonBoundaryDeltaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/LiteralRibbonBoundaryDelta.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the full original flag carrier, deleting a marked ribbon counts its facial class exactly.",
        H("Literal boundary change under signed ribbon deletion"),
        Blocks(
            Paragraph(Text("The input R contains a finite flag carrier, fixed-point-free involutions s and t "
                + "for corners and bands, and the two flags a,b at one end of the mark. The four flags "
                + "a,b,t(a),t(b) are distinct. The physical boundary components are the connected components "
                + "under alternating corner and band steps. The cut fixes these four flags, and the deletion "
                + "caps a with b and t(a) with t(b), leaving every other band step untouched. Thus Delta(R) "
                + "counts the components after those literal same-end caps minus the original number.")),
            Describe.Lean(DescribeId.Create("original-ribbon-boundary-delta"),
                DeclarationHandle.Create(Prefix + "original_boundary_delta"),
                H("The original marked band and its boundary delta"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Bad, good, and regular denote the original directed-face tests BadAt, "
                        + "GoodAt, and RegularAt at the given end of R. The terminology follows "
                        + "Ghanbari and Šámal, Facial diagrams and cycle double cover, arXiv:2605.01410, "
                        + "Sections 1 and 3. The result counts actual original-flag components, not just "
                        + "the orbit classes visible at the four exposed labels.")),
                    Paragraph(Text("The full directed-orbit quotient is the disjoint sum of untouched "
                        + "classes and actual exposed first-return classes. Untouched classes are canonically "
                        + "unchanged by seam replacement. After comparison of the three possible endpoint "
                        + "pairing forms, the directed deltas are +2, 0, and -2. Each undirected alternating "
                        + "component gives two opposite directed cycles, so the corresponding changes "
                        + "are +1, 0, and -1.")),
                    Paragraph(Text("Neither connectedness nor orientability is assumed. Keeping the four "
                        + "attachment flags as dummy subdivisions also retains the boundary of a newly "
                        + "isolated endpoint. A surface realized by a separately constructed flag model, a "
                        + "general one-vertex chart, or a quantum measurement is not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Statement()
    {
        var r = V("R");
        var delta = Call("Delta", r);
        Formula Match(string name, long k) => new Formula.Logic(
            Call(name, r), FormulaLogicOperator.Iff, Equal(delta, k < 0 ? Seq(Minus, Num(-k)) : Num(k)));
        Formula And(Formula a, Formula b) => new Formula.Logic(
            Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
        return Disp(All("R", V("MarkedRibbon"),
            And(Match("Bad", 1), And(Match("Good", 0), Match("Regular", -1)))));
    }
}
