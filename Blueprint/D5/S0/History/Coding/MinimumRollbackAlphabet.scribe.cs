using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Coding;

internal sealed class MinimumRollbackAlphabetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite rollback logs need as many labels as the largest process fiber.",
        H("Minimum Rollback Alphabet"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("largest-process-fiber-is-the-minimum-rollback-alphabet"),
                DeclarationHandle.Create(
                    "D5/S0/History/Coding/MinimumRollbackAlphabet."
                        + "minimum_rollback_alphabet"),
                H("The largest process fiber is the minimum rollback alphabet"),
                StatementSource.FromAuthor(MinimumAlphabetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite state types X and Y and a process U from X to Y, "
                            + "the number mU is computed as the maximum cardinality of an "
                            + "actual fiber of U. Every log whose paired process-log record "
                            + "is injective has an alphabet of cardinality at least mU.")),
                    Paragraph(Text(
                        "Conversely, each fiber is enumerated independently and embedded into "
                            + "the common type Fin mU. Equal process outputs then place two "
                            + "states in the same fiber, while equal labels force equality "
                            + "inside that enumeration, so the paired record is injective.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Nat.card_le_card_of_injective, "
                            + "Finite.equivFin, Fin.castLEEmb, Finset.le_sup, and "
                            + "Finset.sup_le. Repository and pinned-Mathlib searches found no "
                            + "declaration packaging the complete lower bound and attaining "
                            + "construction."))),
                DescribeRole.Theorem))));

    private static Formula Card(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Fiber(Formula process, Formula source, Formula target) =>
        Seq(OpenBrace, source, Colon, Sp, F.Id("X"), Sp, Mid, Sp,
            process, Open, source, Close, Sp, Eq, Sp, target, CloseBrace);

    private static Formula Record(Formula process, Formula log, Formula source) =>
        Seq(Open, process, Open, source, Close, Comma, Sp,
            log, Open, source, Close, Close);

    private static Formula MinimumAlphabetFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula mType = F.Id("M");
        Formula process = F.Id("U");
        Formula log = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula maximum = Seq(F.Id("m"), Underscore, Grp(process));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, yType, Colon, Sp, type, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, xType, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, yType, CloseBracket, Comma, Esc,
            process, Colon, Sp, xType, Sp, To, Sp, yType, Comma, RowBreak,
            maximum, Sp, Eq, Sp, Max, Underscore,
            Grp(y, InMacro, Sp, yType), Sp, Card(Fiber(process, x, y)), Comma, RowBreak,
            Open,
            Forall, Sp, mType, Colon, Sp, type, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, mType, CloseBracket, Comma, Sp,
            log, Colon, Sp, xType, Sp, To, Sp, mType, Comma, RowBreak,
            Operatorname, Grp(F.Id("Injective")), Open,
            x, Sp, Mapsto, Sp, Record(process, log, x), Close, Sp, Rightarrow, Sp,
            maximum, Sp, Leq, Sp, Card(mType),
            Close, Sp, Land, RowBreak,
            Exists, Sp, log, Colon, Sp, xType, Sp, To, Sp,
            Operatorname, Grp(F.Id("Fin")), Open, maximum, Close, Comma, Sp,
            Operatorname, Grp(F.Id("Injective")), Open,
            x, Sp, Mapsto, Sp, Record(process, log, x), Close, Dot));
    }
}
