using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NewmanDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Rewriting/Newman",
                "Terminating locally confluent rewrite systems have unique reachable normal forms."),
            H("Newman Normal Forms"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create(
                        "terminating-locally-confluent-relations-have-unique-normal-forms"),
                    H("Unique reachable normal forms"),
                    LeanTheorem(
                        "D5/S0/Rewriting/Newman.newman_unique_normal_form"),
                    Disp(Seq(
                        Operatorname, Grp(F.Id("WellFounded")), Open,
                        Operatorname, Grp(F.Id("swap")), Open, F.Id("r"), Close, Close,
                        Sp, Land, Sp,
                        Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("a"), Comma, Sp,
                        F.Id("b"), Comma, Sp,
                        F.Id("r"), Open, F.Id("h"), Comma, Sp, F.Id("a"), Close,
                        Sp, Land, Sp,
                        F.Id("r"), Open, F.Id("h"), Comma, Sp, F.Id("b"), Close,
                        Sp, Rightarrow, Sp,
                        Exists, Sp, F.Id("c"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("c"), Close,
                        Sp, Land, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("b"), Comma, Sp, F.Id("c"), Close, Close,
                        Sp, Rightarrow, Sp,
                        Forall, Sp, F.Id("h"), Comma, Sp,
                        Exists, Bang, Sp, F.Id("n"), Comma, Sp,
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("h"), Comma, Sp, F.Id("n"), Close,
                        Sp, Land, Sp,
                        Neg, Exists, Sp, F.Id("x"), Comma, Sp,
                        F.Id("r"), Open, F.Id("n"), Comma, Sp, F.Id("x"), Close, Dot)),
                    DescribeProvenance.LiteratureAttested(Newman),
                    Blocks(
                        Paragraph(Text(
                            "For every terminating and locally confluent rewrite relation, "
                            + "each starting history reaches exactly one irreducible normal "
                            + "form through the reflexive transitive closure of the relation.")),
                        Paragraph(Text(
                            "Newman 1942, literature-attested; this repository gives a direct "
                            + "proof because the pinned Mathlib version does not provide this "
                            + "lemma.")))
                ))));
}
