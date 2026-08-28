using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class ReachableObservableQuotientReachabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability."
            + "reachable_observable_quotient_is_reachable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reachable-observable quotient is spanned by the canonical images of input iterates.",
        H("Reachable Observable Quotient Reachability"),
        Blocks(Describe.Lean(
            DescribeId.Create("reachable-observable-quotient-is-reachable"),
            DeclarationHandle.Create(Declaration),
            H("The minimal quotient remains reachable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The reachable carrier is constructed as the span of the actual input directions "
                    + "and their dynamics iterates. Span induction carries those generators through "
                    + "the canonical quotient by the imported all-future invisible subspace."))),
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

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula input = F.Id("U");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("A");
        Formula control = F.Id("B");
        Formula readout = F.Id("C");
        Formula reachable = F.Id("R");
        Formula invisible = F.Id("Nfuture");
        Formula index = F.Id("k");
        Formula value = F.Id("u");
        Formula generator = Call("mkQ", invisible,
            Call("reachableGenerator", evolution, control, index, value));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, input, Comma, Sp,
            output, Colon, Sp, F.Id("Type"), Comma, Sp,
            evolution, Comma, Sp, control, Comma, Sp, readout, Comma,
            RowBreak, Grp(),
            Call("DivisionRing", scalar), Sp, Land, Sp,
            Call("AddCommGroup", state), Sp, Land, Sp, Call("Module", scalar, state), Sp,
            Land, Sp, Call("AddCommGroup", input), Sp, Land, Sp,
            Call("Module", scalar, input), Comma, RowBreak, Grp(),
            Call("AddCommGroup", output), Sp, Land, Sp, Call("Module", scalar, output), Sp,
            Land, Sp, evolution, Sp, InMacro, Sp, Call("LinearMap", scalar, state, state), Sp,
            Land, Sp, control, Sp, InMacro, Sp, Call("LinearMap", scalar, input, state), Sp,
            Land, Sp, readout, Sp, InMacro, Sp, Call("LinearMap", scalar, state, output), Sp,
            Rightarrow, RowBreak, Grp(),
            Call("let", reachable, Call("reachableSubspace", evolution, control)), Comma, Sp,
            Call("let", invisible,
                Call("comap", Call("eventualKernel", readout, evolution),
                    Call("subtype", reachable))), Comma, RowBreak, Grp(),
            Call("span", scalar,
                Seq(OpenBrace, generator, Sp, Mid, Sp, index, Sp, InMacro, Sp,
                    F.Id("N"), Comma, Sp, value, Sp, InMacro, Sp, input, CloseBrace)),
            Sp, Eq, Sp, F.Id("top"), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
