using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class RelationalPreconditionAdjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relational strongest postconditions are adjoint to universal weakest preconditions.",
        H("Relational Precondition Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relational-adjunction-and-may-not-guarantee"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction."
                        + "relational_adjunction_and_may_not_guarantee"),
                H("Relational adjunction and the may-must distinction"),
                StatementSource.FromAuthor(AdjunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The relation is a set of source-target pairs. The relational strongest "
                            + "postcondition and existential precondition are respectively the "
                            + "pinned library's relational image and preimage. The universal weakest "
                            + "precondition contains states whose every related outcome is in the target.")),
                    Paragraph(Text(
                        "The first displayed conjunct states both directions of the relational "
                            + "adjunction for arbitrary source and target predicates.")),
                    Paragraph(Text(
                        "The remaining public conjuncts use a Boolean relation that allows both "
                            + "outcomes from false and the singleton successful outcome true. A "
                            + "successful path exists, while the false outcome refutes a universal "
                            + "success guarantee."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction"))]));

    private static Formula AdjunctionFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula relation = F.Id("R");
        Formula source = F.Id("P");
        Formula target = F.Id("Q");
        Formula booleanRelation = F.Id("nondeterministicBooleanRelation");
        Formula successful = F.Id("successfulOutcome");
        Formula strongest = Call("relationalStrongestPostcondition", relation, source);
        Formula weakest = Call("universalWeakestPrecondition", relation, target);
        Formula mayCountermodel = Call(
            "existentialPrecondition", booleanRelation, successful);
        Formula mustCountermodel = Call(
            "universalWeakestPrecondition", booleanRelation, successful);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, xType, Comma, Sp, yType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            relation, Colon, Sp, Call("SetRel", xType, yType), Comma, Sp,
            source, Colon, Sp, Call("Set", xType), Comma, Sp,
            target, Colon, Sp, Call("Set", yType), Comma, RowBreak, Grp(),
            Open, strongest, Sp, Subseteq, Sp, target, Sp, Iff, Sp,
            source, Sp, Subseteq, Sp, weakest, Close, Sp, Land, RowBreak, Grp(),
            Open, F.Id("false"), Sp, InMacro, Sp, mayCountermodel, Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open, F.Id("false"), Sp, InMacro, Sp, mustCountermodel, Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
