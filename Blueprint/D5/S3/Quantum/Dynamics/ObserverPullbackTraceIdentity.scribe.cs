using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ObserverPullbackTraceIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated channel evolution and Heisenberg pullback have equal trace readouts.",
        H("Observer Pullback Trace Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-pullback-trace-identity"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Dynamics/ObserverPullbackTraceIdentity."
                    + "observer_pullback_trace_identity"),
            H("Channel iterates equal iterated effect pullbacks"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite carrier is the existing complex matrix algebra. The Schrodinger "
                        + "map is an existing completely positive trace-preserving quantum "
                        + "channel, and rho is an existing positive trace-one density state.")),
                Paragraph(Text(
                    "The Heisenberg map is completely positive and is related to the channel by "
                        + "the displayed one-step trace-duality premise. The effect may be any "
                        + "matrix, so physical effects are included without an extra restriction.")),
                Paragraph(Text(
                    "Induction moves one channel use across the trace pairing at each step. The "
                        + "two canonical iterate recursion laws identify the resulting expression "
                        + "with the same number of Heisenberg pullbacks."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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

    private static Formula Trace(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Tr")), Open, value, Close);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula state = F.Id("X");
        Formula effectVariable = F.Id("A");
        Formula time = F.Id("t");
        Formula channel = Phi;
        Formula heisenberg = Seq(Phi, Caret, Grp(Star));
        Formula rho = Rho;
        Formula effect = F.Id("E");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", d, d, complex);
        Formula channelType = Call("QuantumChannel", d, d);
        Formula heisenbergType = Call("CompletelyPositiveMap", matrix, matrix);
        Formula densityType = Call("DensityState", d);
        Formula channelIterate = Apply(Seq(Open, channel, Close, Caret, Grp(time)), rho);
        Formula pullbackIterate = Apply(Seq(Open, heisenberg, Close, Caret, Grp(time)), effect);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Call("Fintype", d), Comma, Sp, Call("DecidableEq", d), Comma,
            RowBreak, Grp(),
            channel, Colon, Sp, channelType, Comma, Sp,
            heisenberg, Colon, Sp, heisenbergType, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, state, Comma, Sp, effectVariable, Colon, Sp, matrix, Comma, Sp,
            Trace(Seq(Apply(channel, state), Sp, effectVariable)), Sp, Eq, Sp,
            Trace(Seq(state, Sp, Apply(heisenberg, effectVariable))), Close, Comma,
            RowBreak, Grp(),
            time, Colon, Sp, Operatorname, Grp(F.Id("Nat")), Comma, Sp,
            rho, Colon, Sp, densityType, Comma, Sp,
            effect, Colon, Sp, matrix, Comma,
            RowBreak, Grp(),
            Trace(Seq(channelIterate, Sp, effect)), Sp, Eq, Sp,
            Trace(Seq(rho, Sp, pullbackIterate)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
