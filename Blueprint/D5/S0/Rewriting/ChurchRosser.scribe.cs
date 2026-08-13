using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class ChurchRosserDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Relation =
        LibraryNoteRef.Create("D5/L/Rewriting/mathlib-relation");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Global confluence is equivalent to the Church-Rosser convertibility-iff-joinability characterization.",
            H("Church-Rosser Equivalence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("confluence-is-equivalent-to-church-rosser"),
                    DeclarationHandle.Create("D5/S0/Rewriting/ChurchRosser.confluent_iff_church_rosser"),
                    H("Confluence iff convertibility is joinability"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("a"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow,
                        Sp, Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Dot,
                        Iff, Sp,
                        Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("EqvGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp, Iff, Sp,
                        Operatorname, Grp(F.Id("Join")), Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Close, Dot))),
                    AssessedProvenance.FromLiterature(Relation),
                    Blocks(
                        Paragraph(Text(
                            "The forward direction makes joinability an equivalence via "
                            + "Relation.equivalence_join, then eliminates EqvGen by its closure constructors.")),
                        Paragraph(Text(
                            "The reverse direction turns two reductions from one source into "
                            + "a convertibility path through that source. No termination hypothesis is needed.")),
                        Paragraph(Text(
                            "The Newman corollary composes this equivalence with the frozen "
                            + "D5/S0/Rewriting/NewmanConfluence.newman_confluent theorem; "
                            + "Mathlib's Relation.church_rosser remains a stronger sufficient criterion."))),
                    DescribeRole.Theorem)),
                Describe.Lean(
                    DescribeId.Create("newman-termination-and-local-confluence-imply-church-rosser"),
                    DeclarationHandle.Create("D5/S0/Rewriting/ChurchRosser.newman_church_rosser"),
                    H("Newman to Church-Rosser"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open, F.Id("r"), Close, Close,
                        Sp, Land, Sp, Text("local confluence"), Sp, Rightarrow, Sp,
                        Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("EqvGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp, Iff, Sp,
                        Operatorname, Grp(F.Id("Join")), Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Relation),
                    Blocks(Paragraph(Text(
                        "This theorem is a one-composition corollary of the generic equivalence "
                        + "and the frozen Newman confluence theorem."))),
                    DescribeRole.Theorem)))));
}
