using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FiniteCofilteredLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cofiltered limit of nonempty finite sets is nonempty.",
        H("Nonempty Finite Cofiltered Limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-nonempty-cofiltered-limit-is-nonempty"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit."
                    + "finite_cofiltered_limit_nonempty"),
                H("A finite nonempty cofiltered limit is nonempty"),
                StatementSource.FromAuthor(LimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be a cofiltered category and let F assign a type to every object "
                        + "of J. Assume every assigned type is finite and nonempty.")),
                    Paragraph(Text(
                        "The inverse limit is represented by the type of sections compatible "
                        + "with every transition map. That section type is nonempty.")),
                    Paragraph(Text(
                        "Pinned Mathlib already proves this exact statement as "
                        + "nonempty_sections_of_finite_cofiltered_system. The Lean declaration "
                        + "imports and applies that theorem directly; repository search found "
                        + "only a related specialization to invariant candidate subsets."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula LimitFormula()
    {
        Formula index = F.Id("J");
        Formula diagram = F.Id("F");
        Formula j = F.Id("j");
        Formula value = Apply(diagram, j);

        return Disp(Seq(
            Forall, Sp, index, Comma, Sp, diagram, Colon, Sp,
            index, Sp, To, Sp, Operatorname, Grp(F.Id("Set")), Comma, Esc,
            Call("Cofiltered", index), Sp, Land, Esc,
            Open, Forall, Sp, j, InMacro, Sp, index, Comma, Sp,
            Call("Finite", value), Sp, Land, Sp,
            Call("Nonempty", value), Close, Esc,
            Rightarrow, Sp,
            Call("Nonempty", Call("inverseLimit", diagram)), Dot));
    }
}
