using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcSupport;

internal sealed class UniqueChoiceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique existence determines a chosen value and its defining predicate.",
        H("UniqueChoice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unique-choice-uniqueness"),
                DeclarationHandle.Create(Prefix + "choose_uniq"),
                H("Every satisfying value is the chosen value"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Id("x"), F.Comma, F.Sp, Call("p", Id("x")), F.Implies, F.Sp, Id("x"), F.Eq, F.Sp, Choice()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let p be a predicate on any sort and h a proof that exactly one value satisfies p. Every value satisfying p equals Classical.choose! applied to h."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a predicate p on any sort and h witnessing unique existence, Classical.choose!_spec states that the chosen value satisfies p:")),
            Paragraph(Math(F.Disp(Call("p", Choice())))),
            Paragraph(Text("Classical.choose!_eq_iff_right characterizes equality with that value:")),
            Paragraph(Math(F.Disp(F.Seq(F.Forall, F.Sp, Id("x"), F.Comma, F.Sp, Id("x"), F.Eq, F.Sp, Choice(), F.Iff, F.Sp, Call("p", Id("x")))))),
            Paragraph(Text("Classical.choose! is noncomputable and requires a proof of unique existence. Its specification supports retained set definitions and function interpretation; it supplies no new existence axiom or full CSA definition-elimination theorem.")),
            Paragraph(Text("Retained mathematical commands: upstream lines 11-18. The selected definitions and proofs retain Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md.")))));
    private static Formula Choice() =>
        F.Seq(F.Operatorname, F.Grp(F.Id("choose")), F.Bang, F.Open, Id("h"), F.Close);
}
