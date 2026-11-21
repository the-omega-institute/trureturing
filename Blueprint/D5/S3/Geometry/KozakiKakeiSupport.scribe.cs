using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For m at least four, counting nonzero evaluations with two specified true coordinates determines whether those columns are adjacent.",
        H("The signed Boolean support recovers adjacency"),
        Blocks(
            Definition("boolNumber", "Boolean evaluation coordinates",
                "False maps to zero and true maps to one in the complex field."),
            Definition("Cuts", "Matching transversals",
                "A Boolean assignment cuts a matching when the two values on every edge differ."),
            Theorem("eval_matching_ne_zero", "Nonzero matching evaluations",
                "An oriented matching polynomial is nonzero on a Boolean assignment exactly when the assignment cuts every matching edge.",
                EvalMatchingNeZero()),
            Theorem("cuts_separate", "Forcing the two endpoints",
                "If an assignment cuts a matching and the two columns lie on the same edge, their assigned values differ.",
                CutsSeparate()),
            Theorem("signed_support_recovers_adjacency", "Signed support counts detect edges",
                "For an adjacent pair, one matching admits no cuts with both entries true and the other has exactly 2 to the power m−2. For a nonedge both matchings have that many cuts, with at most one common cut. Removing all possible common cancellations leaves strictly more than the edge count when m is at least four.",
                SignedSupportRecoversAdjacency()),
            Theorem("pairSupport_card_invariant", "Scalar symmetry transports support counts",
                "Composition of Boolean assignments with the permutation bijects the two supports. The nonzero scalar preserves the property of evaluating to a nonzero value.",
                PairSupportCardInvariant()),
            Theorem("dihedral_of_scalar_large", "Large-order necessity",
                "Scalar symmetry preserves adjacency by the support count, and the cycle reconstruction forces the relabeling to be dihedral.",
                DihedralOfScalarLarge()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula EvalMatchingNeZero() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("f"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Sp, To, Sp, Word("Bool"), Comma, Sp, Word("eval"), Open,
        Word("boolNumber"), Sp, Circ, Sp, F.Id("f"), Comma, Word("matchingPolynomial"), Open, F.Id("M"), Close,
        Close, Sp, Neq, Sp, D(0), Sp, Iff, Sp, Word("Cuts"), Open, F.Id("M"), Comma, F.Id("f"), Close);

    private static Formula CutsSeparate() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("M"),
        Sp, Colon, Sp, Word("Matching"), Open, F.Id("m"), Close, Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp,
        Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, F.Id("f"), Sp, Colon, Sp, Word("Col"), Open,
        F.Id("m"), Close, Sp, To, Sp, Word("Bool"), Comma, Sp, Word("Cuts"), Open, F.Id("M"), Comma, F.Id("f"),
        Close, Sp, Implies, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp, Word("SameEdge"), Open,
        F.Id("M"), Comma, F.Id("i"), Comma, F.Id("j"), Close, Sp, Implies, Sp, F.Id("f"), Open, F.Id("i"),
        Close, Sp, Neq, Sp, F.Id("f"), Open, F.Id("j"), Close);

    private static Formula SignedSupportRecoversAdjacency() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("i"),
        Comma, F.Id("j"), Sp, Colon, Sp, Word("Col"), Open, F.Id("m"), Close, Comma, Sp, D(4), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp, Open, Word("Adjacent"),
        Open, F.Id("i"), Comma, F.Id("j"), Close, Sp, Iff, Sp, Word("card"), Open, Word("pairSupport"), Open,
        F.Id("i"), Comma, F.Id("j"), Close, Close, Sp, Eq, Sp, D(2), Caret, Grp(F.Id("m"), Minus, D(2)), Close);

    private static Formula PairSupportCardInvariant() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, F.Id("c"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Colon, Sp,
        Word("Col"), Open, F.Id("m"), Close, Comma, Sp, F.Id("c"), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
        Word("rename"), Open, F.Id("s"), Comma, F.Id("F"), Open, F.Id("m"), Close, Close, Sp, Eq, Sp,
        F.Id("C"), Open, F.Id("c"), Close, Sp, Cdot, Sp, F.Id("F"), Open, F.Id("m"), Close, Sp, Implies, Sp,
        Word("card"), Open, Word("pairSupport"), Open, F.Id("s"), Open, F.Id("i"), Close, Comma, F.Id("s"),
        Open, F.Id("j"), Close, Close, Close, Sp, Eq, Sp, Word("card"), Open, Word("pairSupport"), Open,
        F.Id("i"), Comma, F.Id("j"), Close, Close);

    private static Formula DihedralOfScalarLarge() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, F.Id("c"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp, D(4), Sp, Le, Sp, F.Id("m"), Sp, Implies, Sp,
        F.Id("c"), Sp, Neq, Sp, D(0), Sp, Implies, Sp, Word("rename"), Open, F.Id("s"), Comma, F.Id("F"), Open,
        F.Id("m"), Close, Close, Sp, Eq, Sp, F.Id("C"), Open, F.Id("c"), Close, Sp, Cdot, Sp, F.Id("F"), Open,
        F.Id("m"), Close, Sp, Implies, Sp, Word("Dihedral"), Open, F.Id("s"), Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-support-" + name.ToLowerInvariant().Replace('_', '-');
}
