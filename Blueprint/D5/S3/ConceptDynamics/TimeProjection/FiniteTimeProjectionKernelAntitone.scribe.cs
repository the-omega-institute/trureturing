using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TimeProjection;

internal sealed class FiniteTimeProjectionKernelAntitoneDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone."
            + "finite_time_projection_kernel_antitone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality at a longer finite time projection implies equality at every shorter horizon.",
        H("Finite Time Projection Kernel Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-time-projection-kernel-antitone"),
                DeclarationHandle.Create(Gid),
                H("Longer-horizon equality restricts to every shorter horizon"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any state space, readout, update, and horizons N less than or "
                            + "equal to M, equality of the complete readout words through M "
                            + "forces equality of the words through N.")),
                    Paragraph(Text(
                        "The proof embeds each coordinate of Fin (N + 1) into Fin (M + 1) "
                            + "and restricts the assumed function equality along that embedding. "
                            + "Thus the equality kernel is antitone in the horizon."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula readoutType = F.Id("O");
        Formula readout = F.Id("q");
        Formula update = F.Id("tau");
        Formula shorter = F.Id("N");
        Formula longer = F.Id("M");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula word(Formula depth, Formula state) =>
            Call("futureReadoutWord", update, readout, depth, state);

        return Disp(Seq(
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, readoutType), type), Comma, Sp,
            Typed(readout, Arrow(stateType, readoutType)), Comma, Sp,
            Typed(update, Arrow(stateType, stateType)), Comma, RowBreak, Grp(),
            Typed(Seq(shorter, Comma, Sp, longer), naturals), Comma, Sp,
            shorter, Sp, Leq, Sp, longer, Comma, Sp,
            Typed(Seq(left, Comma, Sp, right), stateType), Comma, RowBreak, Grp(),
            Open, word(longer, left), Sp, Eq, Sp, word(longer, right), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, word(shorter, left), Sp, Eq, Sp, word(shorter, right), Close,
            Dot));
    }
}
