using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class InterfaceKernelCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula coarseType = F.Id("A");
        Formula fineType = F.Id("B");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula factor = F.Id("h");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula coarseReadout = Seq(state, Sp, To, Sp, coarseType);
        Formula fineReadout = Seq(state, Sp, To, Sp, fineType);
        Formula fineRange = Seq(Operatorname, Grp(F.Id("range")), Open, fine, Close);
        Formula coarseRange = Seq(Operatorname, Grp(F.Id("range")), Open, coarse, Close);
        Formula fineValue = Seq(
            Operatorname, Grp(F.Id("rangeFactorization")), Open, fine, Comma, Sp, x, Close);
        Formula coarseValue = Seq(
            Operatorname, Grp(F.Id("rangeFactorization")), Open, coarse, Comma, Sp, x, Close);
        Formula factorization = Seq(
            Exists, Bang, Sp, factor, Colon, Sp, fineRange, Sp, To, Sp, coarseRange,
            Comma, Sp, Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            factor, Open, fineValue, Close, Sp, Eq, Sp, coarseValue);
        Formula kernelInclusion = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            fine, Open, x, Close, Sp, Eq, Sp, fine, Open, y, Close, Sp,
            Rightarrow, Sp,
            coarse, Open, x, Close, Sp, Eq, Sp, coarse, Open, y, Close);
        Formula statement = Disp(Seq(
            Forall, Sp, state, Comma, Sp, coarseType, Comma, Sp, fineType,
            Colon, Sp, type, Comma,
            RowBreak, Grp(), coarse, Colon, Sp, coarseReadout, Comma, Sp,
            fine, Colon, Sp, fineReadout, Comma,
            RowBreak, Grp(), Open, factorization, Close, Sp,
            Leftrightarrow, Sp, Open, kernelInclusion, Close, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Interface refinement is exactly reverse inclusion of equality kernels.",
            H("Interface Kernel Criterion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("interface-kernel-criterion"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion."
                            + "interface_refinement_iff_kernel_inclusion"),
                    H("Interface refinement is equivalent to kernel inclusion"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let q and r be interfaces on a shared state carrier, with their "
                                + "codomains restricted canonically to realized images.")),
                        Paragraph(Text(
                            "The interface q is refined by r precisely when there is a unique "
                                + "factor from range(r) to range(q) commuting with the canonical "
                                + "range factorizations. This is equivalent to equality under r "
                                + "always implying equality under q.")),
                        Paragraph(Text(
                            "The proof directly applies the exact observer-memory effective-image "
                                + "kernel criterion, retaining both directions and uniqueness in "
                                + "the public statement."))),
                    DescribeRole.Theorem))));
    }
}
