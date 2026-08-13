using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NewmanConfluenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Terminating locally confluent rewrite systems have globally joinable reductions.",
            H("Newman Confluence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("terminating-locally-confluent-relations-are-confluent"),
                    DeclarationHandle.Create("D5/S0/Rewriting/NewmanConfluence.newman_confluent"),
                    H("Every pair of reductions is joinable"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open, F.Id("r"), Close, Close,
                        Sp, Land, Sp,
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        F.Id("r"), Open, F.Id("h"), Comma, Sp, F.Id("a"), Close,
                        Sp, Land, Sp,
                        F.Id("r"), Open, F.Id("h"), Comma, Sp, F.Id("b"), Close,
                        Sp, Rightarrow, Sp, Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Close,
                        Sp, Rightarrow, Sp,
                        Forall, Sp, F.Id("h"), Comma, Sp, Forall, Sp, F.Id("a"), Comma,
                        F.Id("b"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("a"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow,
                        Sp, Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close, Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(
                        Paragraph(Text(
                            "For every terminating and locally confluent rewrite relation, "
                            + "any two reflexive-transitive reductions from a common source "
                            + "reach a common successor.")),
                        Paragraph(Text(
                            "This corollary reuses the frozen unique-normal-form theorem in "
                            + "D5/S0/Rewriting/Newman; the pinned Mathlib version supplies "
                            + "Relation.ReflTransGen.trans but no matching Newman interface."))),
                    DescribeRole.Theorem))));
}
