using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Factor;

internal sealed class UniqueInterfaceKernelCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion."
            + "unique_interface_factorization_iff_reverse_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique effective-interface factorization is reverse kernel inclusion.",
        H("Unique Interface Kernel Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-interface-kernel-criterion"),
            DeclarationHandle.Create(Declaration),
            H("A unique interface factor exists exactly under reverse kernel inclusion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finer readout is surjective onto its declared carrier, matching the "
                        + "effective-interface convention. The factor and its commuting "
                        + "equation are exposed publicly with uniqueness.")),
                Paragraph(Text(
                    "The imported canonical theorem gives existence exactly from reverse "
                        + "kernel inclusion. Surjectivity then makes any two factors agree on "
                        + "every finer-interface value."))),
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
        Formula coarseType = F.Id("Bq");
        Formula fineType = F.Id("Br");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula factor = F.Id("pi");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula uniqueFactor = Seq(
            Exists, Bang, Sp, factor, Colon, Sp, fineType, Sp, To, Sp, coarseType,
            Comma, Sp, coarse, Sp, Eq, Sp, factor, Sp, Circ, Sp, fine);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coarseType, Comma, Sp, fineType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            coarse, Colon, Sp, state, Sp, To, Sp, coarseType, Comma, Sp,
            fine, Colon, Sp, state, Sp, To, Sp, fineType, Comma, RowBreak, Grp(),
            Call("Surjective", fine), Sp, Rightarrow, RowBreak, Grp(),
            Open, uniqueFactor, Close, Sp, Leftrightarrow, Sp,
            Open, Call("ker", fine), Sp, Subseteq, Sp,
            Call("ker", coarse), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
