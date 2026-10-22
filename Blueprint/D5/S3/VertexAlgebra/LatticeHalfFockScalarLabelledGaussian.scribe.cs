using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockScalarLabelledGaussianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retained Gaussian correction of finite actual oscillator source powers", H("Labelled Gaussian Source Correction"), Blocks(
            Paragraph(Text("D is any finite integral symmetric even-diagonal lattice datum. "
                + "The correction-polynomial result requires no inverse Gram matrix, positivity or occupation bound. "
                + "The original native-field conclusion additionally uses precisely hu:IsUnit D.G.det. "
                + "Its NativeLattice object pairs D with hu, retaining both parameters without extra hypotheses. "
                + "A source direction is a finitely supported complex family f on Index D, and p=sum_i f_i X_i. "
                + "Every frequency is the original sourceWeight(i)=i.2+1. The formal parameter z counts source factors; "
                + "it is not the two-sheet coordinate t and degree n is not a fixed-energy truncation.")),
            Paragraph(Text("The supplier correctedSource is exactly optionEquivLeft.symm composed with "
                + "correctionPolynomial, not a new source map. Its existing multiplication and unit proofs are "
                + "used through exact private constant references without changing their source bodies. "
                + "The finite matching supplier keeps occurrence lists, including repeated colours, before combining coefficients. "
                + "Set P=sum_i f_i (X(some i)+singletonPolynomial(c,i)), "
                + "delta=sum_i f_i pairDerivation(i), and K=sum_i sum_j f_i f_j pairPolynomial(i,j). "
                + "P retains every actual oscillator variable and singleton shift; K uses the original pairScalar, "
                + "with no half inserted in that supplier. All sums here run over the actual finite support of f.")),
            Paragraph(Text("For F_n=correctedSource(c,p^n), the actual insertion operation gives F_(n+1)=(P+delta)F_n. "
                + "The existing singleton and pair correction laws give delta(P)=K and delta(K)=0. "
                + "Induction on the actual source powers proves delta(F_(n+1))=(n+1)K F_n. "
                + "Thus F_(n+2)=P F_(n+1)+(n+1)K F_n, with the true initial polynomials F_0=1 and F_1=P. "
                + "The factor n+1 is derived from the insertion commutator, not imposed as a matching-count assumption. "
                + "The closed formal series is E(z)=exp(Pz+Kz^2/2). Its derivative is (P+Kz)E; "
                + "the coefficient recurrence and its initial coefficients identify F_n=n! [z^n]E. "
                + "The sole unordered-pair factor one half occurs in Kz^2/2; the pairScalar supplier remains unchanged.")),
            Describe.Lean(DescribeId.Create("actual-source-field-gaussian-closed"),
                DeclarationHandle.Create(Prefix + "actual_source_field_gaussian_closed"),
                H("Actual Native Field Of Corrected Source Powers"),
                StatementSource.FromAuthor(Disp(Call("ActualSourceGaussian", F.Id("D"), F.Id("hu"),
                    F.Id("c"), F.Id("f"), F.Id("n")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The exact conclusion is Ytw(D,hu)(single c (p^n)) = n! times "
                    + "nativeCorrectionEvaluation(D,hu,c)([z^n]E). The evaluation is precisely the original finite "
                    + "shiftCoefficients/shiftLinear/normalPolynomial pipeline. It introduces no replacement field or carrier. "
                    + "This is equality of native fields, hence holds at every original mode on every actual target tensor. "
                    + "No infinite coefficient interchange is used in the source-power argument: finite source sums are handled "
                    + "by linearity, and the exponential substitution has zero constant coefficient. "
                    + "This is the classical finite Gaussian/Wick calculation on the actual correction operators, with no novelty claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("This result is a finite-direction source-power bridge, not the all-energy coefficient "
                + "Gaussian identity of creationCoeff(a,j). It does not prove the two-sheet coordinate composition, "
                + "the native charged-product/source-field comparison, or either all-j original iterate identity. "
                + "In particular the original modes -g-j-1 and g-j-1, full q_a=bilinear(a,a), "
                + "g=bilinear(a,b), chargeScalar, ground cocycles, minus-charge monodromy and M-2r remain the "
                + "unchanged obligations of that comparison. The existing cleared-diagonal and below-start results remain "
                + "separate suppliers; no claim is made that importing them closes these gaps. "
                + "The original moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT goal remains open.")))));
}
