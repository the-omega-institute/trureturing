using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.GraphRepresentation;

internal sealed class UniformVertexExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/GraphRepresentation/UniformVertexExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/adamson2026twoword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A representation of a vertex deletion by two k-uniform words extends to the "
        + "whole graph by two (k+1)-uniform words, with an arbitrary neighborhood.",
        H("Uniform Extension by One Vertex"),
        Blocks(
            Paragraph(Text(
                "All vertex types have decidable equality. Finite(V) means V has a finite "
                + "enumeration; an empty V is allowed. Option(V) is the disjoint union of "
                + "the old vertices some(a) and the fresh vertex none. Words are actual "
                + "finite lists. The projection proj(a,b,w) deletes every other letter, "
                + "preserving order and repetitions, using "),
                Ref("D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection"),
                Text(". Natural numbers in the definition below include zero, but the "
                    + "positive condition restricts the representation class to k at least one. "
                    + "No connectedness, nonempty-carrier or neighborhood restriction is imposed.")),
            Describe.Lean(DescribeId.Create("uniform-vertex-ing"),
                DeclarationHandle.Create(Prefix + "InG"),
                H("Positive uniform projection-equality representation"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Both count conditions quantify over every vertex of the same carrier. "
                    + "Their positivity ensures that both word alphabets equal that carrier. "
                    + "For every distinct pair, adjacency holds exactly when the ordered "
                    + "two-letter projections agree. SimpleGraph supplies symmetry and excludes loops."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-vertex-extension"),
                DeclarationHandle.Create(Prefix + "vertex_extension"),
                H("An arbitrary neighborhood costs at most one unit of uniformity"),
                StatementSource.FromAuthor(ExtensionFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The graph D(G) is G.comap(some): its old vertices are V, with "
                    + "D(G).Adj(a,b) equivalent to G.Adj(some(a),some(b)). Choose its "
                    + "representing words w,v. Enumerate old nonneighbors of none once in N "
                    + "and old neighbors once in T. Put Q=NT and construct W=none^k w none NT "
                    + "and Z=none^k v N none T, mapping every old letter through some. "
                    + "Each old vertex occurs k+1 times and none occurs k+1 times in both lists. "
                    + "For an old pair, both projections append the same projection of Q, "
                    + "so right cancellation preserves equality and inequality. For a neighbor a, "
                    + "both fresh/old projections are none^k some(a)^k none some(a). "
                    + "For a nonneighbor a, Z instead projects to none^k some(a)^(k+1) none. "
                    + "After cancelling the common prefix none^k some(a)^k, the remaining heads "
                    + "are none and some(a), hence unequal. Symmetry handles reversed arguments. "
                    + "With no old vertices the words consist of k+1 copies of none.")),
                    Paragraph(Text(
                        "This theorem supplies vertex extension. The all-positive-k adjacent "
                        + "strictness question also needs nonuniversality and a finite minimal "
                        + "nonmember argument; neither conclusion is asserted here."))),
                DescribeRole.Theorem))));

    private static Formula X(string value) => F.Id(value);
    private static Formula Named(string value) => Seq(Operatorname, Grp(X(value)));
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffEq(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Natural() => Seq(Mathbb, Grp(X("N")));
    private static Formula R(Formula k, Formula g) => App("InG", k, g);
    private static Formula Counts(Formula word) =>
        All("a", X("V"), Equal(App("count", X("a"), word), X("k")));
    private static Formula Edges() => All("a", X("V"), All("b", X("V"),
        Imp(Seq(X("a"), Sp, Neq, Sp, X("b")),
            IffEq(App("Adj", X("G"), X("a"), X("b")),
                Equal(App("proj", X("a"), X("b"), X("w")),
                    App("proj", X("a"), X("b"), X("v")))))));
    private static Formula Words() => Seq(Exists, Sp, X("w"), Comma, X("v"), Colon, Sp,
        App("List", X("V")), Comma, Sp,
        And(Counts(X("w")), And(Counts(X("v")), Edges())));
    private static Formula MembershipFormula() => Disp(All("V", Named("Type"),
        All("k", Natural(), All("G", App("SimpleGraph", X("V")),
            IffEq(R(X("k"), X("G")),
                And(Seq(D(0), Sp, Lt, Sp, X("k")), Words()))))));
    private static Formula ExtensionFormula() => Disp(All("V", Named("Type"),
        Imp(App("Finite", X("V")), All("k", Natural(),
            All("G", App("SimpleGraph", App("Option", X("V"))),
                Imp(R(X("k"), App("D", X("G"))),
                    R(Add(X("k"), D(1)), X("G"))))))));
}
