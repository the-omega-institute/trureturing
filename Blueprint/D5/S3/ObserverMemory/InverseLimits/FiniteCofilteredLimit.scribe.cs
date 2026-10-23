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
            new DocumentBlock.Section(H("Countable towers and the finite-layer boundary"), Blocks(
                Paragraph(Text(
                    "Given finite nonempty sets X(n) and arbitrary total maps p(n) from X(n+1) to X(n), "
                    + "Functor.ofOpSequence composes the successor maps into a diagram on the opposite of the "
                    + "natural-number order. Apply nonempty_sections_of_finite_inverse_system to this diagram. "
                    + "A section gives x(n) in X(n) with p(n)(x(n+1)) = x(n) for every n. Surjectivity of the "
                    + "successor maps is not a hypothesis. This is the finite inverse-limit theorem of the "
                    + "Stacks Project, tag 086J.")),
                Paragraph(Text(
                    "Finiteness cannot be omitted: take X(n) to be the natural numbers at least n and take "
                    + "the transition maps to be inclusions. Every level is nonempty, but compatibility makes "
                    + "all selected natural numbers equal to x(0). The level x(0)+1 then requires x(0)+1 at "
                    + "most x(0), a contradiction.")))),
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
                        "The compatible section is an element of the inverse limit. The "
                        + "cofiltered hypothesis permits simultaneous comparison of finitely "
                        + "many indices; finiteness of each component supplies compactness."))),
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
