using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class HindleyRosenDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman1942 =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    private static readonly LibraryNoteRef ChurchRosser1936 =
        LibraryNoteRef.Create("D5/L/Rewriting/churchrosser1936properties");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Strong commutation lifts to closures and makes the union of confluent reductions confluent.",
            H("Hindley-Rosen Confluence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("strong-commutation-lifts-to-reflexive-transitive-closures"),
                    DeclarationHandle.Create("D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute"),
                    H("Strong commutation lifts to closures"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp, F.Id("r"), Open, F.Id("h"), Comma, Sp,
                        F.Id("a"), Close, Sp, Land, Sp, F.Id("s"), Open, F.Id("h"), Comma,
                        Sp, F.Id("b"), Close, Sp, Rightarrow, Sp, Exists, Sp, F.Id("c"), Comma,
                        Sp, F.Id("s"), Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp,
                        Land, Sp, F.Id("r"), Open, F.Id("b"), Comma, Sp, F.Id("c"), Close,
                        Close, Sp, Rightarrow, Sp,
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("a"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("s"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow, Sp,
                        Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("s"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Dot, Close))),
                    AssessedProvenance.FromLiterature(Newman1942),
                    Blocks(Paragraph(Text(
                        "The proof first moves one s-step across an r-closure, then inducts over "
                        + "the s-closure. Each square retains the stated r/s orientation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("hindley-rosen-union-confluence"),
                    DeclarationHandle.Create("D5/S0/Rewriting/HindleyRosen.hindley_rosen_confluent"),
                    H("Confluence of a strongly commuting union"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("Confluent")), Open, F.Id("r"), Close, Sp,
                        Land, Sp, Operatorname, Grp(F.Id("Confluent")), Open, F.Id("s"), Close,
                        Sp, Land, Sp, F.Text, Grp(F.Id("r"), Sp, F.Id("and"), Sp, F.Id("s"),
                        Sp, F.Id("strongly"), Sp, F.Id("commute")), Sp, Rightarrow, Sp,
                        Operatorname, Grp(F.Id("Confluent")), Open, F.Id("r"), Sp, Lor, Sp,
                        F.Id("s"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Newman1942),
                    Blocks(Paragraph(Text(
                        "The union closure is embedded into the closure of alternating r- and "
                        + "s-blocks. Same-color peaks use the two confluence premises, while mixed "
                        + "peaks use lifted commutation; Relation.church_rosser then joins all paths."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("hindley-rosen-church-rosser-characterization"),
                    DeclarationHandle.Create("D5/S0/Rewriting/HindleyRosen.hindley_rosen_church_rosser"),
                    H("Church-Rosser for a strongly commuting union"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("Confluent")), Open, F.Id("r"), Close, Sp,
                        Land, Sp, Operatorname, Grp(F.Id("Confluent")), Open, F.Id("s"), Close,
                        Sp, Land, Sp, F.Text, Grp(F.Id("r"), Sp, F.Id("and"), Sp, F.Id("s"),
                        Sp, F.Id("strongly"), Sp, F.Id("commute")), Sp, Rightarrow, Sp,
                        Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("EqvGen")), Open, F.Id("r"), Sp, Lor, Sp,
                        F.Id("s"), Close, Open, F.Id("a"), Comma, Sp, F.Id("b"), Close,
                        Sp, Iff, Sp, Operatorname, Grp(F.Id("Join")), Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Sp, Lor,
                        Sp, F.Id("s"), Close, Open, F.Id("a"), Comma, Sp, F.Id("b"), Close,
                        Dot, Close))),
                    AssessedProvenance.FromLiterature(ChurchRosser1936),
                    Blocks(Paragraph(Text(
                        "This theorem composes Hindley-Rosen union confluence with the frozen "
                        + "confluence-iff-Church-Rosser equivalence."))),
                    DescribeRole.Theorem))));
}
