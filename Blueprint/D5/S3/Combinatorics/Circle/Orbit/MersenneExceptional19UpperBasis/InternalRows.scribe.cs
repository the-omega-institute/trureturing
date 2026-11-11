using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class InternalRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical internal transport and an integral local inverse.",
        H("Physical internal transport and an integral local inverse"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-internal-bits"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_bits"),
                H("actual internal bits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-internal-readouts"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_readouts"),
                H("actual internal readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-internal-step"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_internal_step"),
                H("selected internal step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-corrected-ladders"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_corrected_ladders"),
                H("selected corrected ladders"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r."))), DescribeRole.Theorem),

            Paragraph(Text("Actual lower words of the differences. For 2<=j<=d-4, the three differences are R_(B/2+2^j)-R_(B/2), R_(B-b-2^j)-R_(B-b-2^(j+1)), and R_(B/2+a-2^j)-R_(B/2+a-2^(j+1)). Every endpoint is itself a selected UPPER row. All three physical words increase by 2^j. The lower j-bit signatures are (beta,0,1-alpha), (0,1-beta,1-sigma), and (sigma,alpha,0), for alpha=bit_j(a), beta=bit_j(b), sigma=bit_j(s).")),
            Paragraph(Text("Deriving the bit signatures. The proof uses divisibility by 2^(j+1) of the high powers. For a negative word -z, bit j complements bit j of z once a lower bit is nonzero. That condition is proved from a,b odd, and from s=2 mod 4 with j>=2. This is a uniform Euclidean-division argument on the actual words, not enumeration of r or a premise containing the claimed coefficient table.")),
            Paragraph(Text("The inverse coefficients. Let T=f+g+h, F=2f-f_next and G=2g-g_next. Under the already proved higher ladder and zero next triple, actual_internal_readouts derives rG=(2alpha-1)T+(1-alpha-beta)F+(1-alpha)G, rF=(2sigma-1)T+(1-sigma)F+(beta-sigma)G, and rH=T-sigma F-alpha G. Put e=alpha+sigma-2alpha sigma, tau=1-beta-e and omega=beta-e. The idempotent equations imply e^2=e and tau*omega=0. Thus L=rG-(2alpha-1)rH=tau F+G and M=rF-(2sigma-1)rH=F+omega G, giving F=M-omega L, G=L-tau M and T=rH+sigma F+alpha G.")),
            Paragraph(Text("A consumed inverse and descending induction. selected_internal_step applies this inverse to the actual vanishing corrected upper readouts, obtaining f_next=2f, g_next=2g, h_next=2h and T=0. selected_corrected_ladders descends from d-3 to 2 and proves Y_(p,j)=2^(j-2)Y_(p,2) and zero corrected triple at every j>=2. No determinant or supplied coefficient formula occurs in its presentation hypothesis.")),
            Paragraph(Text("Source-only boundary. The polynomial inverse and physical carry statements have source scripts, not kernel receipts. The ordinary eight-bit controls are not used as Lean proofs, and no rational-rank argument is used for saturation."))), []));
}
