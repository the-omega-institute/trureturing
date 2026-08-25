using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class KernelRelationInclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula fineType = F.Id("Fine");
        Formula coarseType = F.Id("Coarse");
        Formula fine = F.Id("fine");
        Formula coarse = F.Id("coarse");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula statement = Disp(Seq(
            Forall, Sp, state, Comma, Sp, fineType, Comma, Sp, coarseType,
            Colon, Sp, type, Comma,
            RowBreak, Grp(),
            fine, Colon, Sp, state, Sp, To, Sp, fineType, Comma, Sp,
            coarse, Colon, Sp, state, Sp, To, Sp, coarseType, Comma,
            RowBreak, Grp(),
            Call("Refines", fine, coarse), Sp, Rightarrow, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            fine, Open, x, Close, Sp, Eq, Sp, fine, Open, y, Close, Sp,
            Rightarrow, Sp,
            coarse, Open, x, Close, Sp, Eq, Sp, coarse, Open, y, Close, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A refinement factorization contains the fine equality kernel in the "
                + "coarse equality kernel.",
            H("Kernel Relation Inclusion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("refinement-implies-kernel-relation-inclusion"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Refinement/KernelRelationInclusion."
                            + "refinement_implies_kernel_inclusion"),
                    H("Refinement implies equality-kernel inclusion"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A refinement consists of a coarse-value map together with a "
                                + "commuting equation from the fine readout to the coarse one. "
                                + "Applying that map to equal fine values gives equal coarse "
                                + "values.")),
                        Paragraph(Text(
                            "The formal proof imports the canonical refinement record and "
                                + "directly applies the existing relative-identity refinement "
                                + "theorem's kernel-inclusion conjunct. No parallel refinement "
                                + "or kernel primitive is introduced."))),
                    DescribeRole.Theorem))));
    }
}
