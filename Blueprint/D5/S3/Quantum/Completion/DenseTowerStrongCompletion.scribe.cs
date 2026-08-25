using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class DenseTowerStrongCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Apply(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);

        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula index = F.Id("A");
        Formula stages = F.Id("S");
        Formula stage = F.Id("a");
        Formula vector = F.Id("x");
        Formula stageSpace = Apply(stages, stage);
        Formula projection = Apply(Call("P", stageSpace), vector);
        Formula residual = Apply(
            Grp(Seq(F.Id("I"), Sp, Minus, Sp, Call("P", stageSpace))),
            vector);
        Formula closedSupremum = Seq(
            Overline, Grp(Call("iSup", stage, stageSpace)));

        Formula statement = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, index, Comma, Sp,
                Call("Hilbert", scalar, space), Comma, Sp, Call("Nonempty", index), Comma),
            Seq(
                stages, Colon, Sp, index, Sp, To, Sp, Call("ClosedSubspace", space),
                Comma, Sp, Call("Monotone", stages), Comma),
            Seq(
                closedSupremum, Sp, Eq, Sp, space, Sp, Rightarrow),
            Seq(
                Open, Forall, Sp, vector, InMacro, Sp, space, Comma, Sp,
                Call("lim", stage, Infty, projection), Sp, Eq, Sp, vector,
                Close, Sp, Land),
            Seq(
                Open, Forall, Sp, vector, InMacro, Sp, space, Comma, Sp,
                Call("lim", stage, Infty, new Formula.Norm(residual)),
                Sp, Eq, Sp, D(0), Close, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A dense increasing Hilbert-subspace tower converges strongly to identity.",
            H("Dense-Tower Strong Completion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("dense-tower-projections-converge-strongly"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Completion/DenseTowerStrongCompletion."
                            + "dense_tower_strong_completion"),
                    H("Dense-tower projections converge strongly"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let S be a nonempty directed increasing tower of closed projection "
                                + "subspaces in a Hilbert space. Its closed supremum is assumed "
                                + "to be the whole ambient space.")),
                        Paragraph(Text(
                            "For every fixed vector, the canonical orthogonal projections onto "
                                + "the stages converge in norm to that vector.")),
                        Paragraph(Text(
                            "Subtracting the projection limit from the constant identity vector "
                                + "and applying continuity of the norm gives the equivalent "
                                + "identity-minus-projection residual convergence to zero."))),
                    DescribeRole.Theorem))));
    }
}
