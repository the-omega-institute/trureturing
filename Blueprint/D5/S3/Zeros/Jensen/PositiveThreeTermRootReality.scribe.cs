using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class PositiveThreeTermRootRealityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026dlmforthogonalzeros");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive three-term recurrence excludes a nonreal spectral parameter at a zero.",
        H("Positive Three-Term Root Reality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-positive-three-term-root-reality"),
                DeclarationHandle.Create("D5/S3/Zeros/Jensen/PositiveThreeTermRootReality."
                    + "finite_positive_three_term_zero_has_real_parameter"),
                H("Reality from a finite positive recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let q be any natural number, z any complex number, c a real sequence "
                        + "and v a complex sequence. Assume v_0 is nonzero, v_1=z v_0, and "
                        + "v_(k+2)=z v_(k+1)-c_k v_k with c_k>0 whenever k+2 is at most q. "
                        + "Then v_q=0 implies Im z=0. Both sequences beyond the finite "
                        + "endpoint are unrestricted. The q=0 premises cannot include a zero; "
                        + "at q=1 no recurrence equation or coefficient positivity is required.")),
                    Paragraph(Text(
                        "For Im z nonzero, induction proves v_k nonzero and "
                        + "Im z times Im(v_(k+1)/v_k) positive. The ratio recurrence is "
                        + "v_(k+2)/v_(k+1)=z-c_k/(v_(k+1)/v_k). Its imaginary product "
                        + "equals (Im z)^2 plus c_k times the previous positive product "
                        + "divided by the squared norm of the ratio. This excludes the "
                        + "terminal zero. With c_0=-1, z=i, v_0=1, v_1=i and v_2=0, "
                        + "the endpoint recurrence holds but the parameter is nonreal; "
                        + "coefficient positivity is essential.")),
                    Paragraph(Text(
                        "This is a finite scalar formulation of classical positive-recurrence "
                        + "zero reality, as recorded by DLMF's Favard and orthogonal-polynomial "
                        + "zero results. The direct ratio proof supplies the missing Lean "
                        + "inference without constructing a measure or Jacobi matrix. "
                        + "It carries no literature originality claim, simplicity claim "
                        + "or interlacing claim.")),
                    Paragraph(Text(
                        "For a monic degree-q polynomial satisfying s p''-X p'+q p=0 "
                        + "with real s>0, differentiate the equation at an actual root beta. "
                        + "For q>0, the reversed normalized jets "
                        + "v_k=k! p^(q-k)(beta)/q! through q satisfy this recurrence with "
                        + "z=beta and c_k=s(k+1), with v_0=1, v_1=beta and v_q=0. "
                        + "The theorem therefore supplies the Hermite root-reality endpoint. "
                        + "The degree-zero monic polynomial has no roots. This application "
                        + "does not establish real-rootedness of an original xi core, "
                        + "the signs of its convolution cofactors, or the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
