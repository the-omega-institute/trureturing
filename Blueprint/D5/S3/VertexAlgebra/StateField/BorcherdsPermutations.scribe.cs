using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.StateField;

internal sealed class BorcherdsPermutationsDocument : IScribeDocumentDefinition
{
    private const string Source = "D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed transpositions of Borcherds coefficients",
        H("Signed transpositions of Borcherds coefficients"),
        Blocks(
            Paragraph(Text("Let a_n b denote a family of bilinear integer modes on a complex module. Lower truncation means that a_n b vanishes for all sufficiently large n for each pair of states. Write D(a,b,c;p,q,r) for the forward product minus (-1)^r times the reverse product minus the iterate, with p, q and r arbitrary integers. The binomial coefficients have integer upper indices. Write T^[j] for T^j/j! for a linear endomorphism T.")),
            Describe.Lean(
                DescribeId.Create("borcherds-permutations-defect-identification"),
                DeclarationHandle.Create(Source + "defect_eq_zero_iff_borcherds"),
                H("The coefficient identity as vanishing of the defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under lower truncation, D(a,b,c;p,q,r) vanishes exactly when the Borcherds coefficient identity holds with all three summands finitely supported. The inner modes b_(q+i) c, a_(p+i) c and a_(r+i) b vanish for sufficiently large i, respectively. Bilinearity then kills the summands."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("borcherds-permutations-swap-first"),
                DeclarationHandle.Create(Source + "defect_swap_first"),
                H("Exchange of the first two states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under lower truncation, coefficient skew for (a,b) and the divided state translation law, D(a,b,c;p,q,r) equals (-1)^(r+1) times D(b,a,c;q,p,r). The skew expansion of the iterate is supported on i+j<N by truncation of b_(r+i+j) a. Summing along i+j fixed uses binomial reflection and Vandermonde convolution, via Mathlib's Ring.choose_neg and Ring.add_choose_eq."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("borcherds-permutations-swap-last"),
                DeclarationHandle.Create(Source + "defect_swap_last"),
                H("Exchange of the last two states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under lower truncation and the divided mode translation law for a, assume coefficient skew for (b,c), for (a_(r+i) b,c), and for (b,a_(p+i) c) at every natural i in the two composite families. Then D(a,b,c;p,q,r) is the sum over j at least zero of (-1)^(q+j+1) times T^[j] applied to D(a,c,b;r,q+j,p). The shifted defects themselves have finite support in j. The forward branch has a cutoff from truncation of c_(q+j+i) b. Each composite branch has only finitely many nonzero inner states, and the maximum of their truncation cutoffs bounds j."))),
                DescribeRole.Theorem))));
}
