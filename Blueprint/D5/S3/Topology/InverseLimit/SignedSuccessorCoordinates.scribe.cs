using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedSuccessorCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedSuccessorCoordinates.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Statement() => Disp(Seq(
        All("a", V("Ordinal0")),
        All("H", Call("Prefix", Call("succ", V("a")))),
        All("Y", Call("Set", Call("Space", V("H"), Call("top", V("a"))))),
        All("Z", Call("Set", Call("Space", V("H"), Call("top", V("a"))))),
        Arrow(Call("IsClosed", V("Y")),
        Arrow(Call("IsClosed", V("Z")),
        Arrow(Call("Eq", Call("union", V("Y"), V("Z")), V("univ")),
            Call("Nonempty", Call("Result", V("H"), V("Y"), V("Z"))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual Boolean successor coordinate and all-pairs literal Prefix extension from an arbitrary closed cover.",
        H("Literal successor coordinates"),
        Blocks(
            Paragraph(Text(
                "Use the original SignedProperLimit core: Coord(a) is Iio(a), Cube(a) is Coord(a) to Bool, "
                + "and restrict is literal precomposition with ordinal inclusion. For an arbitrary ordinal a, "
                + "H is a Prefix(succ(a)), top(a) is the index a<succ(a), and K is H.Space(top(a)). "
                + "Y and Z are closed subsets of K with union K. The actual splitCarrier(Y,Z) consists of "
                + "(k,false) for k in Y and (k,true) for k in Z. Overlap retains two separate points. "
                + "Either side may be empty, and a may be zero.")),
            Describe.Lean(
                DescribeId.Create("literal-successor-coordinates"),
                DeclarationHandle.Create(Owner + "exists_successor_coordinates"),
                H("Closed-cover insertion and complete Prefix extension"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Result(H,Y,Z) supplies a closed nonempty carrier C in Cube(succ(a)), an actual homeomorphism "
                        + "e from splitCarrier(Y,Z) onto C, and a Prefix(succ(succ(a))). C is exactly the range of the insertion. "
                        + "For every split point ((k,b),proof) and every i<succ(a), insertion reads k(i) if i<a, and b otherwise; "
                        + "in the latter case i=a. The old-coordinate equation holds at every i<a, the coordinate a is exactly b, "
                        + "and restricting e(x) to a gives k exactly. The inverse reads the old restriction and coordinate a. "
                        + "The homeomorphism proves continuity and both inverse equations.")),
                    Paragraph(Text(
                        "Every old carrier at b<succ(a) is retained as the same set in Cube(b). The new carrier at succ(a) "
                        + "is exactly C. For every b<=a and every z in C, restricting z to b equals restricting the first "
                        + "coordinate of e inverse(z) to b. This equality is used to construct compatibility at every old/new pair. "
                        + "Old/old compatibility and surjectivity come directly from H. For an old/new pair, H.onto first "
                        + "lifts to stage a; the actual cover then supplies a Boolean sheet. Inserting that split point gives "
                        + "the required preimage by the exact restriction equation. Equal new stages use the identity. "
                        + "These are the actual compatible and onto fields of the output Prefix, for all pairs in its domain.")),
                    Paragraph(Text(
                        "Mathlib's Homeomorph.funSplitAt and Homeomorph.piCongrLeft supply function-space splitting and "
                        + "reindexing after identifying the complement of the last ordinal coordinate with Coord(a). "
                        + "Continuous.isClosedEmbedding and Topology.IsEmbedding.toHomeomorph turn the actual continuous "
                        + "injective split insertion into the range homeomorphism. Closedness follows from compactness "
                        + "of the actual closed split inside K times Bool and the Hausdorff target cube. Nonemptiness "
                        + "uses K's existing nonemptiness and the cover's first-projection surjectivity. "
                        + "The new construction is the ordinal coordinate identification and the complete dependent Prefix assembly; "
                        + "the standard topology results and existing Prefix are reused.")),
                    Paragraph(Text(
                        "This local topology supplier assumes no CH, countability, metric structure, proper-stage condition "
                        + "or signed measure system. It does not provide measure transport, a full successor measure system, "
                        + "transfinite recursion, CH bookkeeping or the final topological and analytic endpoints. "
                        + "The construction is repository-derived; no literature novelty or full CH solution is asserted."))),
                DescribeRole.Theorem))));
}
