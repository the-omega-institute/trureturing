using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class DefectScalarBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar transport and middle-energy inequalities for ordered real defects.",
        H("Scalar defect bounds"), Blocks(
            Paragraph(Text("These are consumed scalar helpers of StructuralCone and ActualPSDMoment. " +
                "Their proofs use arbitrary real coordinates and closed inequalities. " +
                "The matrix hypotheses and their consequences are supplied by the calling proofs; " +
                "these scalar statements assert no replacement PSD spectrum or physical realization.")),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-affine-transport"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.affine_defect_transport"),
                H("Affine mass-defect transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real theta,N,j,w,c,E with theta,w nonnegative and j>=6, set " +
                    "L=N+3+2w and a=2 theta L-(2+w). Assume 0<=a<=1/4, " +
                    "theta L^2>=N+11+3w+w^2, E<=5-4w-w^2 and " +
                    "E<=5-4w-w^2+(c-(3-4w))/4. Then " +
                    "(2+w)(N+wj+c)-(1+w)N+E<=theta(N+wj+c)^2. " +
                    "The proof splits at c=3-4w and retains equality and zero-jump cases. " +
                    "StructuralCone.normalized_defect_bound consumes this helper."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-third-head-cap"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.flat_third_head_le_one"),
                H("Third-head cap from the determinant inequality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a,b,e with 0<=e<=b<=a and " +
                    "a^2+b^2+e^2+abe<=4, one has e<=1. " +
                    "The scalar determinant inequality is an explicit premise. " +
                    "Both flat_five_moment and flat_five_middle_energy consume this helper."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-endpoint-order"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.flat_endpoint_ge_third"),
                H("Order of the scalar comparison endpoints"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real e in [0,1], e<=2-e^2. " +
                    "The live consumers are flat_pair_square_le_high and flat_five_moment. " +
                    "The comparison follows from the nonnegative product (1-e)(e+2), including both endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-pair-square-low"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.flat_pair_square_le_low"),
                H("Pair-square comparison below the split"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real a,b,e with e<=a and e<=b, " +
                    "a^2+b^2<=(a+b-e)^2+e^2. " +
                    "No nonnegativity or determinant premise is required. " +
                    "Both flat_five_moment and flat_five_middle_energy consume the comparison."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-pair-square-high"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.flat_pair_square_le_high"),
                H("Pair-square comparison above the split"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a,b,e with 0<=e<=1, a^2+b^2+e^2+abe<=4 and " +
                    "(2-e^2)+e<=a+b, one has a^2+b^2<=(2-e^2)^2+e^2. " +
                    "Both flat_five_moment and flat_five_middle_energy consume this determinant-controlled comparison."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-defect-scalar-five-head-middle-energy"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds.flat_five_middle_energy"),
                H("Ordered five-head middle energy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real w,a,b,e,x,y, assume 2/9<=w<=1/2, a>=1+w, " +
                    "a>=b>=e>=x>=y>=w, a+b+e+x+y<=4-w and a^2+b^2+e^2+abe<=4. " +
                    "Then a(a-w)+b(b-w)+e(e-w)+x(x-w)+y(y-w)<=4-2w-4w^2+w^3+w^4. " +
                    "The original chord is used only at the given five heads. " +
                    "Private scalar comparisons use min(full,truncated), with rational nonnegative polynomial " +
                    "decompositions on the two closed e intervals separated by 3/5. " +
                    "ActualPSDMoment.flat_tail_middle_energy_two_ninths supplies the ordered heads and the determinant premise."))), DescribeRole.Theorem)
        )));
}
