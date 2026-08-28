using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class BirthStageFiltrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every eventually present object in an append-only filtration has a unique first stage.",
        H("Birth Stage Filtration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("birth-stage-is-the-unique-first-stage"),
                DeclarationHandle.Create(Prefix + "birthStage_unique"),
                H("Birth is the unique first stage"),
                StatementSource.FromAuthor(UniqueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a stage family and a node that occurs at some stage. If a chosen "
                            + "level contains the node and every earlier level omits it, that "
                            + "level is the birth stage.")),
                    Paragraph(Text(
                        "The existence, presence, and absence assumptions all appear in the "
                            + "antecedent. Append-only monotonicity is not needed for this "
                            + "uniqueness statement and is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("append-only-stages-retain-born-nodes"),
                DeclarationHandle.Create(Prefix + "mem_of_birthStage_le"),
                H("Append-only stages retain every born node"),
                StatementSource.FromAuthor(PersistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the stage family is append-only and the node eventually appears. "
                            + "Every level at or after its birth contains it.")),
                    Paragraph(Text(
                        "The conclusion is conditional on both eventual presence and the displayed "
                            + "birth-stage inequality; it does not assert earlier membership."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula UniqueFormula()
    {
        Formula carrier = F.Id("V");
        Formula stage = F.Id("stage");
        Formula node = F.Id("node");
        Formula level = F.Id("level");
        Formula earlier = F.Id("earlier");
        Formula present = Seq(node, Sp, InMacro, Sp, Call("stage", level));
        Formula absentEarlier = Seq(
            Forall, Sp, earlier, Colon, Sp, F.Id("Nat"), Comma, Sp,
            earlier, Sp, Lt, Sp, level, Sp, Rightarrow, Sp,
            Neg, Sp, Open, node, Sp, InMacro, Sp, Call("stage", earlier), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stage, Colon, Sp,
            Arrow(F.Id("Nat"), Call("Set", carrier)), Comma, Sp,
            node, Colon, Sp, carrier, Comma, Sp,
            level, Colon, Sp, F.Id("Nat"), Comma, RowBreak, Grp(),
            Open, Exists, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
            node, Sp, InMacro, Sp, Call("stage", F.Id("n")), Close,
            Sp, Land, Sp, present, Sp, Land, RowBreak, Grp(),
            Open, absentEarlier, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("birthStage", stage, node), Sp, Eq, Sp, level, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula PersistenceFormula()
    {
        Formula carrier = F.Id("V");
        Formula stage = F.Id("stage");
        Formula node = F.Id("node");
        Formula level = F.Id("level");
        Formula hypotheses = Seq(
            Call("AppendOnly", stage), Sp, Land, Sp,
            Open, Exists, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
            node, Sp, InMacro, Sp, Call("stage", F.Id("n")), Close,
            Sp, Land, RowBreak, Grp(),
            Call("birthStage", stage, node), Sp, Leq, Sp, level);

        return Disp(Seq(
            Forall, Sp, stage, Colon, Sp,
            Arrow(F.Id("Nat"), Call("Set", carrier)), Comma, Sp,
            node, Colon, Sp, carrier, Comma, Sp,
            level, Colon, Sp, F.Id("Nat"), Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            node, Sp, InMacro, Sp, Call("stage", level), Dot));
    }
}
