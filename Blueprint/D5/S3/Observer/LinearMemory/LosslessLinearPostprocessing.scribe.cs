using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class LosslessLinearPostprocessingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/LosslessLinearPostprocessing."
            + "kernel_comp_eq_iff_injective_on_range";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear postprocessing preserves the observation kernel exactly when it is injective on the observed range.",
        H("Lossless Linear Postprocessing"),
        Blocks(Describe.Lean(
            DescribeId.Create("lossless-linear-postprocessing"),
            DeclarationHandle.Create(Declaration),
            H("Kernel preservation is range injectivity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The forward direction tests two realized observations through their difference. "
                    + "The reverse direction compares each observed value with the observed zero, "
                    + "so injectivity on the realized range recovers the original kernel."))),
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
        Formula observed = F.Id("Y");
        Formula processed = F.Id("Z");
        Formula observation = F.Id("M");
        Formula postprocess = F.Id("B");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, observed, Comma, Sp,
            processed, Colon, Sp, F.Id("Type"), Comma, Sp,
            observation, Comma, Sp, postprocess, Comma,
            RowBreak, Grp(),
            Call("Ring", scalar), Sp, Land, Sp,
            Call("AddCommGroup", state), Sp, Land, Sp, Call("Module", scalar, state), Sp,
            Land, Sp, Call("AddCommGroup", observed), Sp, Land, Sp,
            Call("Module", scalar, observed), Comma, RowBreak, Grp(),
            Call("AddCommGroup", processed), Sp, Land, Sp,
            Call("Module", scalar, processed), Sp, Land, Sp,
            observation, Sp, InMacro, Sp, Call("LinearMap", scalar, state, observed), Sp,
            Land, Sp, postprocess, Sp, InMacro, Sp,
            Call("LinearMap", scalar, observed, processed), Sp, Rightarrow,
            RowBreak, Grp(),
            Call("ker", Call("comp", postprocess, observation)), Sp, Eq, Sp,
            Call("ker", observation), Sp, Iff, Sp,
            Call("InjOn", postprocess, Call("range", observation)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
