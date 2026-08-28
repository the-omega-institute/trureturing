using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class ObservableKrylovPermanentStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability."
            + "observable_krylov_once_stable_permanently";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality of consecutive observable Krylov stages persists at every later stage.",
        H("Observable Krylov Permanent Stability"),
        Blocks(Describe.Lean(
            DescribeId.Create("observable-krylov-once-stable-permanently"),
            DeclarationHandle.Create(Declaration),
            H("One stable observable Krylov step is permanently stable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state and output carriers are finite-dimensional inner-product "
                        + "spaces over a real or complex scalar field. The evolution and "
                        + "readout are arbitrary linear maps on those carriers.")),
                Paragraph(Text(
                    "Each displayed tower stage is the span of the adjoint evolution orbit "
                        + "of the adjoint readout range through the stated depth. Thus the "
                        + "observable object is constructed before stability is asserted.")),
                Paragraph(Text(
                    "Equality of stages m and m plus one makes stage m invariant under the "
                        + "adjoint evolution. Every later generator remains in that stage, "
                        + "while monotonicity supplies the reverse inclusion."))),
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

    private static Formula ObservableStage(
        Formula scalar,
        Formula state,
        Formula output,
        Formula evolution,
        Formula readout,
        Formula depth)
    {
        Formula index = F.Id("k");
        Formula value = F.Id("y");
        Formula adjointEvolution = Grp(evolution, Caret, Grp(Star));
        Formula adjointReadout = Seq(readout, Caret, Grp(Star));
        Formula generator = Seq(
            adjointEvolution, Caret, Grp(index), Open,
            adjointReadout, Open, value, Close, Close);
        return Call(
            "span",
            scalar,
            Seq(OpenBrace, generator, Sp, Mid, Sp,
                D(0), Sp, Le, Sp, index, Sp, Le, Sp, depth,
                Comma, Sp, value, Sp, InMacro, Sp, output, CloseBrace));
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula stage = F.Id("m");
        Formula offset = F.Id("r");
        Formula atStage = ObservableStage(
            scalar, state, output, evolution, readout, stage);
        Formula atSuccessor = ObservableStage(
            scalar, state, output, evolution, readout,
            Seq(stage, Plus, D(1)));
        Formula atOffset = ObservableStage(
            scalar, state, output, evolution, readout,
            Seq(stage, Plus, offset));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Comma, Sp, evolution, Comma, Sp, readout, Comma, Sp, stage, Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Land,
            RowBreak, Grp(),
            evolution, Sp, InMacro, Sp, Call("LinearMap", scalar, state, state), Sp,
            Land, Sp,
            readout, Sp, InMacro, Sp, Call("LinearMap", scalar, state, output), Sp,
            Land, Sp, stage, Sp, InMacro, Sp, F.Id("N"), Sp, Rightarrow,
            RowBreak, Grp(),
            atStage, Sp, Eq, Sp, atSuccessor, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, offset, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
            atOffset, Sp, Eq, Sp, atStage, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
