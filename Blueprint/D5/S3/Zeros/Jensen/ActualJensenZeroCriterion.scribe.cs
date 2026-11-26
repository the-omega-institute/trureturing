using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class ActualJensenZeroCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local uniform approximation by the actual fixed-shift theta Jensen polynomials gives a zero-exclusion criterion.",
        H("Cauchy zero exclusion for the actual Jensen tower"),
        Blocks(
            Describe.Lean(DescribeId.Create("all-roots-real"),
                DeclarationHandle.Create(Prefix + "AllRootsReal"),
                H("Real roots of a complex polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex polynomial p, AllRootsReal(p) says that every complex z with p(z)=0 has imaginary part zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("locally-uniform-real-rooted-limit"),
                DeclarationHandle.Create(Prefix + "allZerosReal_of_locallyUniform"),
                H("Cauchy zero exclusion under locally uniform limits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let l be any nontrivial filter on any index type. Let p be a family of complex polynomials whose evaluations converge locally uniformly throughout the complex plane along l to an entire function F. Assume F(0) is nonzero and eventually along l each p has only real roots. Then every complex zero of F has imaginary part zero.")),
                    Paragraph(Text("Around a putative nonreal zero of F, choose a disk within the complement of the real axis and small enough to isolate the zero. The boundary minimum of the norm of F is positive. A sufficiently close polynomial is zero-free throughout the disk and has norm at least half that minimum on the boundary. Cauchy's order-zero estimate for its reciprocal gives the same lower bound on the polynomial's norm at the center, contradicting convergence there."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-equals-xi-square"),
                DeclarationHandle.Create(Prefix + "sourceF_eq_xiSquareSource"),
                H("The theta source in the xi-square coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire theta cosine-square source F equals the normalized xi-square function as a function on the whole complex plane. The latter evaluates xi at one half plus i times a square root of z and divides by xi at one half. Apply the theta Fourier identity to both signs of the square root. Xi reflection identifies the two readings, and the cosine identity takes their average."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-jensen-reflection"),
                DeclarationHandle.Create(Prefix + "sourceJensen_real_iff_reflected"),
                H("Invariance of root reality under reflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural degree d, the actual sourceJensenPolynomial(d) has only real roots if and only if sourcePolynomial(d) has only real roots. The second is the first composed with X mapped to minus X, which sends roots by z mapped to minus z."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-from-actual-jensen-tower"),
                DeclarationHandle.Create(Prefix + "rh_of_actual_jensen_tower"),
                H("Riemann hypothesis from every positive degree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the actual fixed zero-shift sourceJensenPolynomial(d) has only real roots for every natural d at least one. Then the Riemann hypothesis holds.")),
                    Paragraph(Text("The reflected polynomials converge locally uniformly to the theta cosine-square source by the fixed-window approximation estimate, and the source takes value one at zero. Cauchy zero exclusion puts all its zeros on the real axis. For a nontrivial zeta zero s, its square-source coordinate is the square of minus i times (s minus one half). Its imaginary part is twice Im(s) times (one half minus Re(s)). Zeta has no real zero in the open critical interval, so Re(s) equals one half."))),
                DescribeRole.Theorem))));
}
