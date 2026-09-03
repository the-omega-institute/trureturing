using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class WithinRoundCouplingSameLayerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer."
            + "within_round_coupling_is_same_layer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coupled recorded round is a same-layer augmented system, without an automatic "
            + "self-description closure implication.",
        H("Within-Round Coupling and Same-Layer Evaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("within-round-coupling-is-same-layer"),
                DeclarationHandle.Create(Declaration),
                H("Coupling places both observers on one layer"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let e be a positive round index. The append-only operations R and "
                            + "the maps q1 : X -> A, controlledUpdate : RoundIndex -> "
                            + "X x Y2 -> X, and q2 : Lambda1 -> Y2 are exactly the data of "
                            + "the recorded observer at that round.")),
                    Paragraph(Text(
                        "WithinRoundDecoupled says that controlledUpdate e has the same value "
                            + "for every pair of Y2 inputs at each state. The theorem assumes "
                            + "the negation of precisely that condition.")),
                    Paragraph(Text(
                        "The first public conjunct is IsSameLayerInRound. Its joint state is "
                            + "X x Lambda1, its update substitutes q2(lambda) into the controlled "
                            + "update, and its joint readout is (q1(x), q2(lambda)). On the kernel "
                            + "quotient of that readout, the canonical q2 evaluation is indexed "
                            + "twice by the same quotient and its diagonal is q2 itself.")),
                    Paragraph(Text(
                        "The second public conjunct negates "
                            + "SameLayerSelfDescriptionClosureAutomatic. Expanded, it says that "
                            + "there is no universal rule taking every same-layer recorded round "
                            + "to surjectivity of its canonical q2 evaluation. This coupled round "
                            + "is the counterexample. Coupling supplies "
                            + "two distinct Y2 values; swapping one with the other and sending all "
                            + "remaining values to the first gives a fixed-point-free twist. The "
                            + "imported Lawvere diagonal theorem then supplies the missing table.")),
                    Paragraph(Text(
                        "Thus the second conjunct is a non-implication statement. It does not "
                            + "claim that every enriched or higher-layer closure is impossible."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula record = new Formula.Subscript(F.Id("Lambda"), D(1));
        Formula reading = F.Id("A");
        Formula secondOutput = new Formula.Subscript(F.Id("Y"), D(2));
        Formula round = F.Id("RoundIndex");
        Formula recordOps = F.Id("R");
        Formula q1 = F.Id("q1");
        Formula update = F.Id("controlledUpdate");
        Formula q2 = F.Id("q2");
        Formula e = F.Id("e");
        Formula recordOpsType = Call("AppendOnlyOps", record, reading);
        Formula q1Type = Arrow(state, reading);
        Formula updateType = Arrow(round, Arrow(Call("Prod", state, secondOutput), state));
        Formula q2Type = Arrow(record, secondOutput);
        Formula coupled = new Formula.Not(Call("WithinRoundDecoupled", update, e));
        Formula sameLayer = Call(
            "IsSameLayerInRound", recordOps, q1, update, q2, e);
        Formula notAutomatic = new Formula.Not(
            Call("SameLayerSelfDescriptionClosureAutomatic",
                state, record, reading, secondOutput));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, record, Comma, Sp, reading, Comma, Sp,
            secondOutput, Colon, Sp, type, Comma, Esc,
            recordOps, Colon, Sp, recordOpsType, Comma, Esc,
            q1, Colon, Sp, q1Type, Comma, Esc,
            update, Colon, Sp, updateType, Comma, Esc,
            q2, Colon, Sp, q2Type, Comma, Esc,
            e, Colon, Sp, round, Comma, Esc,
            Open, coupled, Close, Sp, Rightarrow, Esc,
            Open, sameLayer, Close, Sp, Land, Esc,
            Open, notAutomatic, Close, Dot));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
}
