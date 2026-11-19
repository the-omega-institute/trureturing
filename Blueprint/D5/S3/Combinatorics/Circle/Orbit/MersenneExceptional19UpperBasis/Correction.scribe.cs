using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class CorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer correction incidence before torsion-sensitive descent.",
        H("Integer correction incidence before torsion-sensitive descent"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-correction-read"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.physical_correction_read"),
                H("physical correction read"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-correction-integer-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.affine_correction_integer_zero"),
                H("affine correction integer zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corrected-affine-read"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.corrected_affine_read"),
                H("corrected affine read"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-corrected-high"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.selected_corrected_high"),
                H("selected corrected high"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations."))), DescribeRole.Theorem),

            Paragraph(Text("The physical correction vector. The six nonzero entries of C are C_(1,d-3)=1, C_(1,d-2)=1, C_(2,d-2)=-1, C_(0,d-1)=-1, C_(1,d-1)=2 and C_(2,d-1)=-2. correctionBlock expresses C*theta by reusing the sealed first, middle and last normal-form functions with zero geometric generators. correctedBlock subtracts it from the original physical block labels. highTheta is exactly 2*g_(d-3)-g_(d-2).")),
            Paragraph(Text("Integer incidence, then arbitrary groups. The shared physical readouts and top_digits prove that reading correctionBlock on chi(L,M,U) equals correction(B,L,M,U)*theta. For a permitted affine row, the sealed affine_digits theorem already proves correction=0 in Z. affine_correction_integer_zero records this actual integer incidence, and corrected_affine_read consumes it to preserve the affine readout for arbitrary A. This reuses the stronger existing integer digit fact directly; it performs no cancellation of Q, 2 or any other scalar inside A.")),
            Paragraph(Text("Starting the descent. The six actual high equations from HighRows show that at levels d-3,d-2,d-1, the corrected blocks equal a single triple, twice that triple and four times that triple, with its sum zero. These are the initial invariants used by selected_corrected_ladders. They are derived from the selected presentation, rather than requested as assumptions in the final reconstruction.")),
            Paragraph(Text("The correction is computed from actual binary digits with integer coefficients. Its affine incidence vanishes before scalar multiplication in the target group, so no cancellation of a possibly nonunit scalar in an abelian group is used."))), []));
}
