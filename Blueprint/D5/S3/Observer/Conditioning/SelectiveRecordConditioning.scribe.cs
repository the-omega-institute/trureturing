using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class SelectiveRecordConditioningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero record branch determines its normalized selective system state.",
        H("Selective Record Conditioning"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-record-branch-forces-the-selective-state"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/SelectiveRecordConditioning."
                        + "selective_record_conditioning"),
                H("A nonzero record branch forces the selective state"),
                StatementSource.FromAuthor(ConditioningFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a finite complex matrix and let P_k be the matrix selected "
                            + "by a record value k. The supplied branch law says that multiplying "
                            + "the conditioned state rho_k by its Born weight recovers the "
                            + "unnormalized compression P_k rho P_k.")),
                    Paragraph(Text(
                        "When the Born weight is nonzero, scalar cancellation uniquely determines "
                            + "rho_k. The proof uses the field inverse law and scalar associativity; "
                            + "the conditioned state is not defined to be the displayed target."))),
                DescribeRole.Theorem))));

    private static Formula ConditioningFormula()
    {
        Formula n = F.Id("n"), labels = F.Id("K"), index = F.Id("k");
        Formula p = F.Id("P"), rho = Rho;
        Formula conditioned = Seq(Rho, Underscore, Grp(index));
        Formula projection = new Formula.Subscript(p, index);
        Formula matrix = MatrixType(n);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finiteN = Seq(
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, n, Close, CloseBracket);
        Formula weight = Call("Tr", Seq(rho, Sp, projection));
        Formula branch = Seq(projection, Sp, rho, Sp, projection);

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, labels, Colon, Sp, type, Comma, Sp,
            finiteN, Comma, RowBreak,
            Grp(), p, Colon, Sp, labels, Sp, To, Sp, matrix, Comma, Sp,
            rho, Comma, Sp, conditioned, Colon, Sp, matrix, Comma, RowBreak,
            Grp(), index, Sp, InMacro, Sp, labels, Comma, Sp,
            weight, Sp, Neq, Sp, D(0), Comma, RowBreak,
            Grp(), weight, Sp, conditioned, Sp, Eq, Sp, branch, Sp, Rightarrow, RowBreak,
            Grp(), conditioned, Sp, Eq, Sp,
            new Formula.Fraction(branch, weight), Dot));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);
}
