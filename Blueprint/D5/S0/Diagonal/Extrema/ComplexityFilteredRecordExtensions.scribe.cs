using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Extrema;

internal sealed class ComplexityFilteredRecordExtensionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var filtered = Seq(
            OpenBrace, F.Id("f"), Sp, Mid, Sp,
            Call("complexity", F.Id("f")), Sp, Le, Sp, F.Id("Q"), CloseBrace);
        var restricted = Call(
            "RestrictedExtensions", filtered, F.Id("record"), F.Id("prescribed"));
        var freeChoices = new Formula.Power(
            Call("card", F.Id("Y")),
            Seq(Call("card", F.Id("D")), Sp, Minus, Sp, Call("card", F.Id("record"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite complexity filters eventually contain every record extension.",
            H("Complexity-Filtered Record Extensions"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("complexity-filters-eventually-attain-the-full-count"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/Extrema/ComplexityFilteredRecordExtensions."
                            + "restricted_extension_card_eventually_eq"),
                    H("Complexity filters eventually attain the full extension count"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Exists, Sp, F.Id("Qstar"), Comma, Sp,
                        Forall, Sp, F.Id("Q"), Sp, Ge, Sp, F.Id("Qstar"), Comma, Sp,
                        Call("card", restricted), Sp, Eq, Sp, freeChoices))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The finite function space D to Y has a maximum complexity value. "
                                + "Choose Qstar as that maximum. Every function then belongs to "
                                + "each complexity filter at level Q at least Qstar.")),
                        Paragraph(Text(
                            "The filtered candidate set is therefore the full function space. "
                                + "The exact record-extension cardinality theorem then gives "
                                + "card(Y) raised to card(D) minus card(record).")),
                        Paragraph(Text(
                            "This closes the qualitative part of the source clause: existence of "
                                + "a uniform finite complexity threshold, eventual containment of "
                                + "every record extension, and eventual equality of the "
                                + "restricted-extension cardinality. The source's explicit "
                                + "quantitative threshold bound Q* <= K(R) + (N0-n) ceil(log m) "
                                + "+ c log N0 REMAINS OPEN and is not discharged.")),
                        Paragraph(Text(
                            "The repository and pinned Mathlib were searched before proving. No "
                                + "theorem matching the full statement was found. The proof uses "
                                + "Finset.sup, Finset.le_sup, and record_extension_card."))),
                    DescribeRole.Theorem))));
    }
}
