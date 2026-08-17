using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class InterventionNaturalityMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naturality on every nonempty address type forces transition commutation and the "
            + "minimal controlled behavior factor.",
        H("Intervention Naturality Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intervention-naturality-forces-the-minimal-behavior-factor"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/InterventionNaturalityMinimality."
                        + "intervention_naturality_minimality"),
                H("Intervention naturality forces the minimal behavior factor"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite controlled state carrier Y map surjectively to a finite "
                            + "realization W while preserving its current readout. Assume that "
                            + "pointwise projection commutes with every input-indexed twisted "
                            + "diagonal for every nonempty address type and every table.")),
                    Paragraph(Text(
                        "Specializing the address type to Unit and the sole table entry to an "
                            + "arbitrary state recovers each transition equation. The theorem "
                            + "then applies the existing controlled-behavior universal property "
                            + "to obtain the unique surjective factor from W to the complete "
                            + "behavior quotient, including its projection, update, and readout "
                            + "equations.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Function.semiconj_iff_comp_eq for converting "
                            + "the singleton calculation to a function equation. Repository "
                            + "search supplied controlled_behavior_universal_property for the "
                            + "quotient conclusion; both declarations are applied directly."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula MinimalityFormula()
    {
        Formula input = F.Id("u");
        Formula update = F.Id("F");
        Formula realization = F.Id("r");
        Formula realizedUpdate = F.Id("G");
        Formula factor = F.Id("h");
        Formula projection = Pi;
        Formula completion = F.Id("Z");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, input, Comma, Sp,
            Call("DiagonalNatural", realization, Apply(update, input),
                Apply(realizedUpdate, input)), Close, Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, input, Comma, Sp,
            realization, Sp, Circ, Sp, Apply(update, input), Sp, Eq, Sp,
            Apply(realizedUpdate, input), Sp, Circ, Sp, realization, Close, Sp,
            Land, RowBreak,
            Open, Exists, Bang, Sp, factor, Colon, Sp, F.Id("W"), Sp, To, Sp,
            completion, Comma, Sp, Call("Surjective", factor), Sp, Land, Sp,
            projection, Sp, Eq, Sp, factor, Sp, Circ, Sp, realization, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
