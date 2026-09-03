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
        "The source coupling implication is retained, while the current same-layer "
            + "encoding is explicitly recorded as unconditional.",
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
                        "CrossRoundUpdateSchedule records the separate inter-round clause. The "
                            + "update at nextRound e is selected by a function receiving q2 of "
                            + "the preceding round's terminal record. IsSecondLayerObserver is the "
                            + "all-round predicate requiring WithinRoundDecoupled at every round.")),
                    Paragraph(Text(
                        "The first public conjunct is IsSameLayerInRound. Its definition contains "
                            + "exactly the two clauses in Definition 45.2: jointRoundUpdate is "
                            + "pointwise the displayed Definition 45.1 update, and q2 evaluation "
                            + "on the joint quotient is the same-typed diagonal self-application. "
                            + "Failure of decoupling is not part of this conclusion predicate.")),
                    Paragraph(Text(
                        "The current encoding proves IsSameLayerInRound for every round update, "
                            + "without using the coupling premise, because both clauses are "
                            + "definitional equalities. This fidelity boundary remains open. "
                            + "Re-entry requires a source-supported account of q2 evaluation as "
                            + "same-layer self-application that is not definitionally true for "
                            + "every update; no source-unsupported conjunct may be added.")),
                    Paragraph(Text(
                        "The second conjunct is EstablishedClosureNonimplications, definitionally "
                            + "the proposition already proved by closure_nonimplication_triple for "
                            + "Sections 32.10 and 33.10. No universal surjectivity predicate or "
                            + "round-specific closure semantics is introduced here. The cited "
                            + "countermodels say only that the closures are not implied; they do "
                            + "not say that every enriched closure is impossible."))),
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
        Formula establishedNonimplications = F.Id("EstablishedClosureNonimplications");

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
            Open, establishedNonimplications, Close, Dot));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
}
