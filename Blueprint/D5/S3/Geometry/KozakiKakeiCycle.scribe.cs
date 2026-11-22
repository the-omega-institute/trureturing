using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiCycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two unordered matchings partition the edges of the cycle on the columns.",
        H("Recovering the cycle from its two matchings"),
        Blocks(
            Definition("step", "Cyclic successor",
                "The successor adds one modulo 2m."),
            Definition("Adjacent", "Cycle adjacency",
                "Two columns are adjacent when either is the successor of the other."),
            Definition("SameEdge", "Membership in a matching edge",
                "The two columns form an edge of the given matching in one of its two orders."),
            Theorem("step_val", "Successor index",
                "The value of the successor is the remainder of the index plus one modulo 2m.",
                StepVal()),
            Theorem("step_ne", "Successor is distinct",
                "The cycle has at least four columns, so its successor has no fixed point.",
                StepNe()),
            Theorem("adjacent_ne", "Adjacent vertices are distinct",
                "Both orientations of adjacency relate distinct columns.",
                AdjacentNe()),
            Theorem("odd_forward", "Orientation of odd edges",
                "The second end of every odd matching edge is the successor of its first end.",
                OddForward()),
            Theorem("even_forward", "Orientation of interior even edges",
                "The second end of each nonclosing even edge is the successor of its first end.",
                EvenForward()),
            Theorem("even_closing", "Orientation of the closing edge",
                "The first end of the closing even edge is the successor of its second end.",
                EvenClosing()),
            Theorem("sameEdge_iff", "Recognizing a matching edge",
                "For distinct columns, their inverse images under the matching have the same edge index exactly when they form a matching edge.",
                SameEdgeIff()),
            Theorem("edges_cover", "Cycle edge coverage",
                "An unordered pair of distinct columns is adjacent exactly when it belongs to the odd or even matching.",
                EdgesCover()),
            Theorem("edges_disjoint", "Disjoint cycle matchings",
                "An unordered pair of distinct columns cannot be an edge of both matchings.",
                EdgesDisjoint()),
            Theorem("dihedral_of_preserves_adjacency", "Exact cycle reconstruction",
                "The images of zero and one select a start and an orientation. Injectivity forces each successive image to use the neighbor different from the preceding image. This determines a rotation or a reflection on the complete cycle.",
                DihedralOfPreservesAdjacency()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula StepVal() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp, F.Id("m"), Sp,
        Implies, Sp, Word("val"), Open, Word("step"), Open, F.Id("i"), Close, Close, Sp, Eq, Sp, Open,
        Word("val"), Open, F.Id("i"), Close, Plus, D(1), Close, Sp, Word("mod"), Sp, Open, D(2), Sp, Cdot, Sp,
        F.Id("m"), Close);

    private static Formula StepNe() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp, F.Id("m"), Sp,
        Implies, Sp, Word("step"), Open, F.Id("i"), Close, Sp, Neq, Sp, F.Id("i"));

    private static Formula AdjacentNe() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Word("Adjacent"), Open, F.Id("i"), Comma, F.Id("j"), Close, Sp, Implies,
        Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"));

    private static Formula OddForward() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("e"),
        Sp, Colon, Sp, Word("Fin"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp, F.Id("m"), Sp,
        Implies, Sp, Word("step"), Open, Word("oddVertex"), Open, F.Id("e"), Comma, Word("false"), Close,
        Close, Sp, Eq, Sp, Word("oddVertex"), Open, F.Id("e"), Comma, Word("true"), Close);

    private static Formula EvenForward() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("e"),
        Sp, Colon, Sp, Word("Fin"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp, F.Id("m"), Sp,
        Implies, Sp, Word("val"), Open, F.Id("e"), Close, Sp, Neq, Sp, D(0), Sp, Implies, Sp, Word("step"),
        Open, Word("evenVertex"), Open, F.Id("e"), Comma, Word("false"), Close, Close, Sp, Eq, Sp,
        Word("evenVertex"), Open, F.Id("e"), Comma, Word("true"), Close);

    private static Formula EvenClosing() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("e"),
        Sp, Colon, Sp, Word("Fin"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp, F.Id("m"), Sp,
        Implies, Sp, Word("val"), Open, F.Id("e"), Close, Sp, Eq, Sp, D(0), Sp, Implies, Sp, Word("step"),
        Open, Word("evenVertex"), Open, F.Id("e"), Comma, Word("true"), Close, Close, Sp, Eq, Sp,
        Word("evenVertex"), Open, F.Id("e"), Comma, Word("false"), Close);

    private static Formula SameEdgeIff() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp,
        Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp,
        Implies, Sp, Open, Word("SameEdge"), Open, F.Id("M"), Comma, F.Id("i"), Comma, F.Id("j"), Close, Sp,
        Iff, Sp, Open, Exists, Sp, F.Id("e"), Sp, Colon, Sp, Word("Fin"), Open, F.Id("m"), Close, Comma, Sp,
        Open, F.Id("i"), Eq, F.Id("M"), Open, F.Id("e"), Comma, Word("false"), Close, Sp, Land, Sp, F.Id("j"),
        Eq, F.Id("M"), Open, F.Id("e"), Comma, Word("true"), Close, Close, Sp, Lor, Sp, Open, F.Id("i"), Eq,
        F.Id("M"), Open, F.Id("e"), Comma, Word("true"), Close, Sp, Land, Sp, F.Id("j"), Eq, F.Id("M"), Open,
        F.Id("e"), Comma, Word("false"), Close, Close, Close, Close);

    private static Formula EdgesCover() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp, Open, Word("Adjacent"),
        Open, F.Id("i"), Comma, F.Id("j"), Close, Sp, Iff, Sp, Open, Word("SameEdge"), Open,
        Word("oddMatching"), Open, F.Id("m"), Close, Comma, F.Id("i"), Comma, F.Id("j"), Close, Sp, Lor, Sp,
        Word("SameEdge"), Open, Word("evenMatching"), Open, F.Id("m"), Close, Comma, F.Id("i"), Comma,
        F.Id("j"), Close, Close, Close);

    private static Formula EdgesDisjoint() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp, Word("SameEdge"), Open,
        Word("oddMatching"), Open, F.Id("m"), Close, Comma, F.Id("i"), Comma, F.Id("j"), Close, Sp, Implies,
        Sp, Neg, Word("SameEdge"), Open, Word("evenMatching"), Open, F.Id("m"), Close, Comma, F.Id("i"), Comma,
        F.Id("j"), Close);

    private static Formula DihedralOfPreservesAdjacency() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, D(2), Sp, Le,
        Sp, F.Id("m"), Sp, Implies, Sp, Open, Forall, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Comma, Sp, Word("Adjacent"), Open, F.Id("i"), Comma, F.Id("j"),
        Close, Sp, Implies, Sp, Word("Adjacent"), Open, F.Id("s"), Open, F.Id("i"), Close, Comma, F.Id("s"),
        Open, F.Id("j"), Close, Close, Close, Sp, Implies, Sp, Word("Dihedral"), Open, F.Id("s"), Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-cycle-" + name.ToLowerInvariant().Replace('_', '-');
}
