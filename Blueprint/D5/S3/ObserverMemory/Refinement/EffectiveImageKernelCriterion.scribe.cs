using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class EffectiveImageKernelCriterionDocument : IScribeDocumentDefinition
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
            "Refinement on realized images is exactly reverse inclusion of equality kernels.",
            H("Effective Image Kernel Criterion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("effective-image-refinement-kernel-criterion"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Refinement/"
                            + "EffectiveImageKernelCriterion."
                            + "refinement_iff_kernel_inclusion_on_effective_images"),
                    H("Effective-image refinement is equivalent to kernel inclusion"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let q and r be readouts on the same state carrier. Refinement is "
                                + "stated directly on their realized codomains: there is a unique "
                                + "map from range(r) to range(q) commuting with both canonical "
                                + "range factorizations.")),
                        Paragraph(Text(
                            "Any such factor sends equal r-values to equal q-values. Conversely, "
                                + "if equality under r always implies equality under q, selecting "
                                + "a source representative of each realized r-value constructs "
                                + "the factor, and kernel inclusion makes that construction "
                                + "independent of the representative.")),
                        Paragraph(Text(
                            "The proof directly reuses Set.rangeFactorization, Set.rangeSplitting, "
                                + "and their exact computation lemmas. The existing refinement "
                                + "family supplies the canonical Concept carrier; no parallel "
                                + "readout or refinement structure is declared."))),
                    DescribeRole.Theorem))));
    }
}
