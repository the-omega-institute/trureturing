using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class LookupProgramUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lookup compiler bounds the least cost of a total program consistent with a record.",
        H("Lookup Program Upper Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lookup-program-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound.lookup_program_upper_bound"),
                H("A table-lookup program bounds the spectrum bottom"),
                StatementSource.FromAuthor(LookupFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A LookupCompiler assigns each finite record a total program that agrees "
                        + "with the record. Its cost field states that this explicit lookup program "
                        + "uses at most the record-description cost plus a fixed overhead.")),
                    Paragraph(Text(
                        "The spectrum bottom is the least natural-number cost among all total "
                        + "programs consistent with the record. The compiled lookup program is a "
                        + "member of that class, so minimality gives the displayed upper bound.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no matching description-complexity model. The proof "
                        + "therefore keeps the program and consistency semantics explicit while "
                        + "reusing Nat.find_min' for the least-witness inequality."))),
                DescribeRole.Theorem)),
        []));

    private static Formula LookupFormula()
    {
        Formula recordType = F.Id("Record"), programType = F.Id("TotalProgram");
        Formula consistent = F.Id("consistent"), programCost = F.Id("programCost");
        Formula recordComplexity = F.Id("recordComplexity"), overhead = F.Id("overhead");
        Formula compiler = F.Id("compiler"), record = F.Id("record");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula consistencyType = Seq(
            programType, Sp, To, Sp, recordType, Sp, To, Sp, proposition);
        Formula compilerType = Seq(
            Operatorname, Grp(F.Id("LookupCompiler")), Open,
            recordType, Comma, Sp, programType, Comma, Sp, consistent, Comma, Sp,
            programCost, Comma, Sp, recordComplexity, Comma, Sp, overhead, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, recordType, Comma, Sp, programType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Forall, Sp, consistent, Colon, Sp, consistencyType,
            Comma, RowBreak, Grp(),
            Forall, Sp, programCost, Colon, Sp,
            programType, Sp, To, Sp, natural, Comma, RowBreak, Grp(),
            Forall, Sp, recordComplexity, Colon, Sp,
            recordType, Sp, To, Sp, natural, Comma, Sp,
            overhead, Colon, Sp, natural, Comma, RowBreak, Grp(),
            Forall, Sp, compiler, Colon, Sp, compilerType,
            Comma, RowBreak, Grp(),
            Forall, Sp, record, Colon, Sp, recordType, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("spectrumBottom")), Open,
            compiler, Comma, Sp, record, Close, Sp, Leq, Sp,
            Operatorname, Grp(recordComplexity), Open, record, Close,
            Sp, Plus, Sp, overhead, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
