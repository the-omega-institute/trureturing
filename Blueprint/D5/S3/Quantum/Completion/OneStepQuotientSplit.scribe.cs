using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class OneStepQuotientSplitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One orthogonal shell canonically splits successive Hilbert quotients.",
        H("One-Step Quotient Split"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-quotient-split-exact"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/OneStepQuotientSplit."
                        + "one_step_quotient_split_exact"),
                H("One orthogonal shell gives a split quotient sequence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be the old visible subspace of a real-or-complex Hilbert "
                            + "space and E an orthogonal shell. The next visible space is "
                            + "constructed as E plus S, and both quotient maps are the "
                            + "canonical submodule quotient maps.")),
                    Paragraph(Text(
                        "The shell map is injective, the step map is surjective, and the "
                            + "range of the former is exactly the kernel of the latter. The "
                            + "public computation rule sends e to its class modulo S.")),
                    Paragraph(Text(
                        "The named kernel equivalence and second-isomorphism-law equivalence "
                            + "identify both the kernel and the literal successive quotient "
                            + "with E. The named Hilbert equivalence splits the old quotient "
                            + "as the L2 product of E and the next quotient, with E as its "
                            + "first coordinate.")),
                    Paragraph(Text(
                        "The proof applies the repository's canonical quotient-orthogonal "
                            + "isometry and Mathlib's factor map, kernel formula, second "
                            + "isomorphism law, and orthogonal decomposition. No existing "
                            + "declaration combined all public clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("k"), space = F.Id("H");
        Formula oldSpace = F.Id("S"), shell = F.Id("E"), element = F.Id("e");
        Formula next = Seq(shell, Sp, Plus, Sp, oldSpace);
        Formula shellMap = Call("shellEmbedding", oldSpace, shell);
        Formula step = Call("stepMap", oldSpace, shell);
        Formula kernelEquiv = Call("shellKernelEquiv", oldSpace, shell);
        Formula layerEquiv = Call("successiveQuotientShellEquiv", oldSpace, shell);
        Formula split = Call("quotientShellSplit", oldSpace, shell);
        Formula oldQuotient = Call("Quotient", space, oldSpace);
        Formula nextQuotient = Call("Quotient", space, next);
        Formula layerQuotient = Call("Quotient", next, oldSpace);
        Formula shellImage = Apply(shellMap, element);
        Formula shellClass = Call("class", element, oldSpace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, oldSpace, Comma, Sp, shell,
            Comma, RowBreak, Grp(),
            Call("Hilbert", scalar, space), Comma, Sp,
            Call("HasOrthogonalProjection", oldSpace), Comma, Sp,
            Call("HasOrthogonalProjection", next), Comma, RowBreak, Grp(),
            Call("Complete", shell), Comma, Sp, oldSpace, Sp, Perp, Sp, shell,
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Call("Injective", shellMap), Sp, Land, Sp,
            Call("Surjective", step), Sp, Land, RowBreak, Grp(),
            Call("range", shellMap), Sp, Eq, Sp, Call("ker", step), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, element, InMacro, Sp, shell, Comma, Sp,
            shellImage, Sp, Eq, Sp, shellClass, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, element, InMacro, Sp, shell, Comma, Sp,
            Apply(kernelEquiv, element), Sp, Eq, Sp, shellImage, Close,
            Sp, Land, RowBreak, Grp(),
            layerEquiv, Colon, Sp, layerQuotient, Sp, To, Sp, shell, Sp, Land,
            RowBreak, Grp(),
            split, Colon, Sp, oldQuotient, Sp, To, Sp,
            Call("L2Sum", shell, nextQuotient), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, element, InMacro, Sp, shell, Comma, Sp,
            Call("fst", Apply(split, shellImage)), Sp, Eq, Sp, element, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
