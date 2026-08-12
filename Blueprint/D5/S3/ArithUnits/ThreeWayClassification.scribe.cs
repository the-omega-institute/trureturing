using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class ThreeWayClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-element classification is not equivalent to a two-element residue grading.",
        H("Three-Way Classification Is Not Binary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-way-classification-is-not-binary"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/ThreeWayClassification.three_way_classification_not_binary"),
                H("A three-way classification is not a binary grading"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("Equiv")), Open,
                    Operatorname, Grp(F.Id("Fin")), Open, D(3), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("ZMod")), Open, D(2), Close,
                    Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is an honest partial closure of the source's non-binary clause. "
                        + "It formalizes only the cardinality obstruction between a three-element "
                        + "classification and the two-element residue grading.")),
                    Paragraph(Text(
                        "The source's self-description limitations, copying obstruction, "
                        + "fixed-point-count interpretation, and parity-shadow claim remain "
                        + "unresolved and are outside this deposit.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No exact theorem was found. "
                        + "The Lean declaration is a thin wrapper around Fintype.card_congr and "
                        + "ZMod.card: an equivalence would force the unequal cardinalities three "
                        + "and two to coincide."))),
                DescribeRole.Theorem))));
}
