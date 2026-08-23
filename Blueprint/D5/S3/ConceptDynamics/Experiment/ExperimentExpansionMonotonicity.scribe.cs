using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class ExperimentExpansionMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding the allowed experiments can only shrink state indistinguishability.",
        H("Experiment Expansion and Indistinguishability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("experiment-expansion-shrinks-indistinguishability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity."
                        + "expansion_shrinks_indistinguishability"),
                H("Experiment expansion shrinks indistinguishability"),
                StatementSource.FromAuthor(ExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed response map, two states are indistinguishable relative "
                            + "to an allowed experiment set when every experiment in that set "
                            + "returns the same response on both states.")),
                    Paragraph(Text(
                        "If the original experiments are contained in an expanded set, agreement "
                            + "under every expanded experiment includes agreement under every "
                            + "original one. Thus expansion can remove indistinguishable pairs "
                            + "but cannot create them.")),
                    Paragraph(Text(
                        "The proof views each relation as a bounded intersection of equal-response "
                            + "sets and applies Mathlib's bounded-intersection inclusion law."))),
                DescribeRole.Theorem))));

    private static Formula ExpansionFormula()
    {
        Formula experimentType = F.Id("E");
        Formula stateType = F.Id("X");
        Formula responseType = F.Id("R");
        Formula original = F.Id("original");
        Formula expanded = F.Id("expanded");
        Formula run = F.Id("run");
        Formula experimentSet = Call("Set", experimentType);
        Formula runType = Seq(
            experimentType, Sp, To, Sp, stateType, Sp, To, Sp, responseType);
        Formula expandedRelation = Call(
            "experimentIndistinguishability", expanded, run);
        Formula originalRelation = Call(
            "experimentIndistinguishability", original, run);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, experimentType, Comma, Sp, stateType, Comma, Sp,
            responseType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            original, Comma, Sp, expanded, Colon, Sp, experimentSet, Comma,
            RowBreak, Grp(),
            run, Colon, Sp, runType, Comma,
            RowBreak, Grp(),
            original, Sp, Subseteq, Sp, expanded, Sp, Rightarrow,
            RowBreak, Grp(),
            expandedRelation, Sp, Subseteq, Sp, originalRelation, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
