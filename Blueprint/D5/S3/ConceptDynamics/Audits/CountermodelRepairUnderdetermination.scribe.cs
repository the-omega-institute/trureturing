using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class CountermodelRepairUnderdeterminationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/CountermodelRepairUnderdetermination."
            + "countermodel_diagnosis_is_underdetermined";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One countermodel supports assumption restriction and conclusion enlargement without "
            + "selecting between them.",
        H("Countermodel Repair Underdetermination"),
        Blocks(Describe.Lean(
            DescribeId.Create("countermodel-repair-underdetermination"),
            DeclarationHandle.Create(Declaration),
            H("A countermodel diagnoses failure without uniquely prescribing repair"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A state in the assumption-minus-conclusion set witnesses the advertised "
                        + "four-way diagnosis: the conclusion fails there, the assumptions do "
                        + "not entail it, the state may be excluded by a stricter assumption "
                        + "set, or a purported derivation of the invalid entailment is refuted.")),
                Paragraph(Text(
                    "Restricting the assumptions away from the witness and enlarging the "
                        + "conclusion to include it are both strict changes. Each construction "
                        + "strictly reduces the corresponding countermodel set, so the original "
                        + "countermodel alone does not choose the repair direction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("M");
        Formula assumptions = F.Id("A");
        Formula conclusion = F.Id("P");
        Formula inferenceRule = F.Id("R");
        Formula model = F.Id("m");
        Formula revised = F.Id("Aprime");
        Formula candidate = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula modelSet = Call("Set", modelType);
        Formula countermodels = Seq(assumptions, Sp, Setminus, Sp, conclusion);
        Formula restricted = Seq(
            OpenBrace, candidate, Sp, Mid, Sp,
            candidate, Sp, InMacro, Sp, assumptions, Sp, Land, Sp,
            candidate, Sp, Neq, Sp, model, CloseBrace);
        Formula enlarged = Seq(
            OpenBrace, candidate, Sp, Mid, Sp,
            candidate, Sp, InMacro, Sp, conclusion, Sp, Lor, Sp,
            candidate, Sp, Eq, Sp, model, CloseBrace);

        Formula diagnosis = Seq(
            Neg, Sp, Open, model, Sp, InMacro, Sp, conclusion, Close, Sp, Lor,
            RowBreak, Grp(),
            Neg, Sp, Open, assumptions, Sp, Subseteq, Sp, conclusion, Close,
            Sp, Lor,
            RowBreak, Grp(),
            Open, Exists, Sp, revised, Colon, Sp, modelSet, Comma, Sp,
            revised, Sp, Subset, Sp, assumptions, Sp, Land, Sp,
            Neg, Sp, Open, model, Sp, InMacro, Sp, revised, Close, Close, Sp, Lor,
            RowBreak, Grp(),
            Open, Call("Derives", inferenceRule, assumptions, conclusion),
            Sp, Land, Sp,
            Neg, Sp, Open, assumptions, Sp, Subseteq, Sp, conclusion, Close,
            Close);

        Formula repairs = Seq(
            restricted, Sp, Subset, Sp, assumptions, Sp, Land,
            RowBreak, Grp(),
            Open, restricted, Sp, Setminus, Sp, conclusion, Close,
            Sp, Subset, Sp, countermodels, Sp, Land,
            RowBreak, Grp(),
            conclusion, Sp, Subset, Sp, enlarged, Sp, Land,
            RowBreak, Grp(),
            Open, assumptions, Sp, Setminus, Sp, enlarged, Close,
            Sp, Subset, Sp, countermodels);

        return Disp(Seq(
            Forall, Sp, modelType, Colon, Sp, type, Comma, Sp,
            assumptions, Comma, Sp, conclusion, Colon, Sp, modelSet, Comma, Sp,
            inferenceRule, Colon, Sp,
            modelSet, Sp, To, Sp, modelSet, Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            model, Colon, Sp, modelType, Comma,
            RowBreak, Grp(),
            model, Sp, InMacro, Sp, countermodels, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, diagnosis, Close, Sp, Land,
            RowBreak, Grp(),
            Open, repairs, Close, Dot));
    }
}
