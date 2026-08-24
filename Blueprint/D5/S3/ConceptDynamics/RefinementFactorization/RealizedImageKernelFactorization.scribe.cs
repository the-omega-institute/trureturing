using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class RealizedImageKernelFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula coarseType = F.Id("A");
        Formula fineType = F.Id("B");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula factor = F.Id("h");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula coarseReadout = Seq(state, Sp, To, Sp, coarseType);
        Formula fineReadout = Seq(state, Sp, To, Sp, fineType);
        Formula fineRange = Call("range", fine);
        Formula coarseRange = Call("range", coarse);
        Formula coarseEffective = Call("rangeFactorization", coarse);
        Formula fineEffective = Call("rangeFactorization", fine);
        Formula uniqueFactorization = Seq(
            Exists, Bang, Sp, factor, Colon, Sp, fineRange, Sp, To, Sp, coarseRange,
            Comma, Sp, coarseEffective, Sp, Eq, Sp,
            factor, Sp, Circ, Sp, fineEffective);
        Formula kernelInclusion = Seq(
            Call("ker", fine), Sp, Subseteq, Sp, Call("ker", coarse));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coarseType, Comma, Sp, fineType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            coarse, Colon, Sp, coarseReadout, Comma, Sp,
            fine, Colon, Sp, fineReadout, Comma, RowBreak, Grp(),
            Open, uniqueFactorization, Close, Sp, Leftrightarrow, Sp,
            Open, kernelInclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Realized-image factorization is unique exactly under reverse kernel inclusion.",
            H("Realized-Image Kernel Factorization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("realized-image-unique-factorization-kernel-criterion"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/RefinementFactorization/"
                            + "RealizedImageKernelFactorization."
                            + "realized_image_unique_factorization_iff_reverse_kernel"),
                    H("Realized-image factorization is the reverse kernel criterion"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The two readouts are restricted canonically to their realized "
                                + "codomains by Set.rangeFactorization. The public factor is "
                                + "unique and its commuting equation is stated directly.")),
                        Paragraph(Text(
                            "The existence equivalence is obtained by applying the imported "
                                + "effective_refines_iff_reverse_kernel theorem to those two "
                                + "surjective readouts. Their kernels are identified with the "
                                + "original equality kernels by the pinned Mathlib equality API.")),
                        Paragraph(Text(
                            "Surjectivity of the finer range factorization then forces any two "
                                + "commuting factors to agree on every realized value. No parallel "
                                + "refinement or kernel-inclusion criterion is reconstructed."))),
                    DescribeRole.Theorem))));
    }

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
}
