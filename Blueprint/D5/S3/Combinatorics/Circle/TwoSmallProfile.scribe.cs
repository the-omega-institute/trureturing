using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TwoSmallProfileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period-closing rigidity for two SMALL gaps",
        H("Period-closing rigidity for two SMALL gaps"),
        Blocks(
            Paragraph(Text("The physical source is centered modulo N=2^k-1. A label is SMALL when its absolute increment is less than Q=2^(k-2); all other labels are LARGE. Physical occurrences are counted even when their numerical values coincide.")),
            Describe.Lean(DescribeId.Create("large-gap-profile"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallProfile.large_gap_profile"),
                H("Signed values along a LARGE arc"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A SMALL departure w(0) with 0<w(0)<Q is followed by ell physical LARGE occurrences, with N=4Q-1 and centered bounds [-2Q+1,2Q-1]. For every j<=ell the sign is paritySign(j), and 3w(j+1)=paritySign(j)N+2^j(6w(0)-N). This includes the endpoint after the last LARGE step. The proof uses the actual strict branches of centered doubling; each LARGE step changes sign and the bounded odd-modulus interval prevents zero at that step."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("large-gap-endpoint"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallProfile.large_gap_endpoint"),
                H("The endpoint magnitude"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The endpoint has positive magnitude paritySign(ell)w(ell+1), and three times that magnitude equals N+(-2)^ell(6w(0)-N). Multiplication by the accumulated sign converts the signed arc formula into this magnitude identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closing-classifier"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallProfile.closing_classifier"),
                H("Solving the two period equations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If AB=Q, N=4Q-1>0 and C=2Q-1, and the two actual return magnitudes obey 3r=N+A(6s-N), 3s=N+B(6r-N), then 3s=C-B and 3r=C-A. Elimination produces N(3s-C+B)=0 and its symmetric counterpart; positivity of N permits cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-two-gap-classifier"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallProfile.cyclic_two_gap_classifier"),
                H("Two physical gaps close with the same parity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a bounded centered-doubling sequence close after ell+m+2 steps, have positive SMALL value at zero, a second SMALL at ell+1, and LARGE values at every other physical position. Let Q=2^(ell+m), N=4Q-1 and C=2Q-1. Then ell and m have the same parity. With r=paritySign(ell)w(ell+1), one has r>0, 3w(0)=C-(-2)^m and 3r=C-(-2)^ell, together with the complete signed formulas on both arcs. Applying the first arc formula to the sign-normalized second arc makes period closure force equal parity signs. Their product is one, so (-2)^ell(-2)^m=Q, and the closing classifier fixes the magnitudes."))),
                DescribeRole.Theorem),
            Paragraph(Text("The mathematical source context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This result treats exactly two physical SMALL labels. Arbitrary-defect completion and the full global strict lexicographic exchange remain open."))), []));
}
