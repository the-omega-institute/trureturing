using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthMainTermsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar logarithmic integrals control the single-length main terms.",
        H("Single-length main terms"),
        Blocks(
            Paragraph(Text(
                "Write B=1−γ−log(2π) and M_k(Y,v)=μ_k v^(k/2) times the integral "
                + "of (log(y/v)+B)^(k/2) from 1 to Y, with μ_2=1 and μ_4=3. "
                + "The logarithm integral gives the exact second main term. "
                + "Pointwise logarithm and power differences control rounding of the length; "
                + "the integral on the terminal interval controls rounding of the cutoff.")),
            Describe.Lean(
                DescribeId.Create("floor-log-difference"),
                DeclarationHandle.Create(Prefix + "floor_log_difference"),
                H("Logarithmic floor error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For v at least one, the absolute difference between log v and the logarithm of its natural floor is at most the reciprocal of that floor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-main-exact"),
                DeclarationHandle.Create(Prefix + "second_main_exact"),
                H("Second main exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Y at least one and v positive, the second main term equals v·[Y log(Y/v)+(B−1)Y+1+log v−B]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-main-second"),
                DeclarationHandle.Create(Prefix + "length_main_second"),
                H("Length main second"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 2≤Y and 1≤v≤Y, rounding v down changes the second main term by at most C Y log Y, for an absolute positive constant C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-main-fourth"),
                DeclarationHandle.Create(Prefix + "length_main_fourth"),
                H("Length main fourth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 2≤Y and 1≤v≤Y, rounding v down changes the fourth main term by at most C Y v (log Y)², for an absolute positive constant C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-main-term"),
                DeclarationHandle.Create(Prefix + "cutoff_main_term"),
                H("Cutoff main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For moment order two or four, 2≤Y, and integer length 1≤K≤Y, rounding Y down changes the main term by at most C K^(k/2) (log Y)^(k/2)."))),
                DescribeRole.Theorem))));
}
