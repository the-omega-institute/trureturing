using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class GlobalDiscriminantSplitKernelChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global equivalence refines discriminant equivalence, which refines split equivalence.",
        H("Global, Discriminant, and Split Relations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("global-discriminant-split-kernel-chain"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ObservationOrder/"
                        + "GlobalDiscriminantSplitKernelChain."
                        + "global_discriminant_split_kernel_chain"),
                H("The promised relation direction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three public relations are constructed as the equality kernels of "
                            + "the global classifier, discriminant readout, and split readout on "
                            + "one common state carrier.")),
                    Paragraph(Text(
                        "Preservation of the discriminant is expressed by its factorization "
                            + "through the global classifier. Dependence of the split result only "
                            + "on the discriminant is the second canonical refinement.")),
                    Paragraph(Text(
                        "Applying kernel monotonicity to those two factorizations gives the stated "
                            + "chain. No claim of local equivalence, genus equivalence, spinor-"
                            + "genus equivalence, or class-group identification is inferred.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact theorem packaging "
                            + "both inclusions. The proof applies the existing single-step relative "
                            + "identity refinement theorem twice."))),
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
        Formula state = F.Id("X");
        Formula globalValue = F.Id("G");
        Formula discriminantValue = F.Id("D");
        Formula splitValue = F.Id("S");
        Formula global = F.Id("global");
        Formula discriminant = F.Id("discriminant");
        Formula split = F.Id("split");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula hypotheses = Seq(
            Call("Refines", discriminant, global), Sp, Land, Sp,
            Call("Refines", split, discriminant));
        Formula conclusion = Seq(
            Call("ker", global), Sp, Subseteq, Sp, Call("ker", discriminant),
            Sp, Land, Sp,
            Call("ker", discriminant), Sp, Subseteq, Sp, Call("ker", split));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, globalValue, Comma, Sp,
            discriminantValue, Comma, Sp, splitValue, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            global, Colon, Sp, state, Sp, To, Sp, globalValue, Comma, Sp,
            discriminant, Colon, Sp, state, Sp, To, Sp, discriminantValue,
            Comma, Sp, split, Colon, Sp, state, Sp, To, Sp, splitValue,
            Comma, RowBreak, Grp(),
            hypotheses, RowBreak, Grp(),
            Rightarrow, Sp, conclusion, Dot));
    }
}
