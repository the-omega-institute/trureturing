using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCreationEnergyContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCreationEnergyContraction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original creation energy and full retained pair contractions", H("Actual Creation Energy"), Blocks(
            Paragraph(Text("D is the unrestricted original finite integral symmetric even-diagonal lattice datum. "
                + "The source and output charges are arbitrary, and no positivity, nondegeneracy or occupation cutoff is used. "
                + "F_e is correctedSource(c,creationCoeff(a,e)), using the original creation exponential and original correction. "
                + "Its integer e is oscillator energy, not the number of factors of a finite source direction. "
                + "The retained polynomial keeps the original variables X(some i) and the original shift variable X(none).")),
            Describe.Lean(DescribeId.Create("actual-retained-creation-energy-contraction"),
                DeclarationHandle.Create(Prefix + "actual_retained_creation_energy_contraction"),
                H("Full Retained Energy Contraction"),
                StatementSource.FromAuthor(Disp(Call("RetainedCreationEnergyContraction", F.Id("D"),
                    F.Id("a"), F.Id("c"), F.Id("e"), F.Id("i")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every natural e and original index i, delta_i(F_e) is the finite sum over r=1,...,e of "
                    + "pairScalar(weight(i),r) times bilinear(unitCharge(i),a)/r, "
                    + "times X(none)^(weight(i)+r) F_(e-r). "
                    + "The supplier pairScalar remains unchanged, and no unordered-pair half is inserted here. "
                    + "The proof uses the original exponential derivation and annihilation law, not a new exponential model. "
                    + "The completed original correction partial law is reused exactly. "
                    + "A finite variable-derivation expansion is extended to all source frequencies below e only after "
                    + "the derivatives above e have been proved zero. Repeated labels and every retained variable survive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-retained-creation-energy-recurrence"),
                DeclarationHandle.Create(Prefix + "actual_retained_creation_energy_recurrence"),
                H("Actual Energy Insertion Recurrence"),
                StatementSource.FromAuthor(Disp(Call("RetainedCreationEnergyRecurrence", F.Id("D"),
                    F.Id("a"), F.Id("c"), F.Id("e")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The original creation exponential gives (e+1) F_(e+1) as the finite sum over frequencies k=0,...,e "
                    + "and original lattice coordinates l of a_l times insertion_(l,k)(F_(e-k)). "
                    + "The factor e+1 is derived by extracting an actual energy coefficient of the original exponential derivative. "
                    + "The original correctedSource multiplication law transports that equation through the full finite correction. "
                    + "This is an identity of retained polynomials, not a recurrence imposed on an abstract sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-native-creation-energy-recurrence"),
                DeclarationHandle.Create(Prefix + "actual_native_creation_energy_recurrence"),
                H("Original Native Field Energy Recurrence"),
                StatementSource.FromAuthor(Disp(Call("NativeCreationEnergyRecurrence", F.Id("D"),
                    F.Id("hu"), F.Id("a"), F.Id("c"), F.Id("e")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "With precisely hu:IsUnit D.G.det, the insertion and contraction identities are transported through "
                    + "the existing nativeCorrectionEvaluation. The left side is the original Ytw of single c creationCoeff(a,e+1). "
                    + "The right side retains all normal variables and singleton terms, plus the exact finite pair contractions "
                    + "and original shift powers. The equality is one of actual native fields and therefore holds at every "
                    + "integer mode on every actual target tensor. All new interchanges are finite sums; the normalPolynomial, "
                    + "shiftCoefficients and shiftLinear evaluation remains the original one. "
                    + "This is the source-side energy recurrence, not the charged-product branch recurrence or its identification."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-creation-energy-gaussian-recurrence"),
                DeclarationHandle.Create(Prefix + "actual_creation_energy_gaussian_recurrence"),
                H("Original Energy Scalar Gaussian Recurrence"),
                StatementSource.FromAuthor(Disp(Call("ActualEnergyScalarGaussianRecurrence", F.Id("D"),
                    F.Id("a"), F.Id("b"), F.Id("j")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Put c=a+b, q=bilinear(a,a) and g=bilinear(a,b), with the full signed integral form. "
                    + "G_j is obtained from correctedSource(c,creationCoeff(a,j)) by the exact algebra evaluation "
                    + "X(some i)=0 and X(none)=1. Thus j is the energy coefficient of the original creation exponential. "
                    + "With b_m=halfBinomial(m), h_m=(q+g)b_m/m+q/(2m) times the finite sum "
                    + "of b_r b_(m-r) over r=1,...,m-1. The theorem proves jG_j as the finite sum "
                    + "of m h_m G_(j-m) over m=1,...,j. It is derived from the actual insertion and contraction laws. "
                    + "The triangular finite sum is regrouped by total energy; reflecting each finite diagonal "
                    + "pairs its two ordered weights and yields exactly one factor of one half. "
                    + "No separate pair half is imposed on the original contraction. The coordinate sums use the original bilinear form. "
                    + "This is an exact source-scalar projection, not a vacuum matrix element or a charged-product branch comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-creation-energy-gaussian-closed"),
                DeclarationHandle.Create(Prefix + "actual_creation_energy_gaussian_closed"),
                H("Original Energy Scalar Gaussian Coefficients"),
                StatementSource.FromAuthor(Disp(Call("ActualEnergyScalarGaussianClosed", F.Id("D"),
                    F.Id("a"), F.Id("b"), F.Id("j")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every natural energy j, the same actual G_j equals the j-th coefficient "
                    + "of the formal exponential of the series with coefficients h_m. Its constant coefficient is one: "
                    + "this is proved from the original creation exponential and correctedSource(1)=1. "
                    + "The original recurrence and the formal exponential derivative then identify all coefficients "
                    + "by induction. No recurrence of the charged product, analytic branch choice, "
                    + "positive lattice hypothesis or replacement Ytw is assumed. "
                    + "The proof retains the full q, signed g and original c=a+b. "
                    + "This scalar coefficient identity does not identify the full retained normal-jet operator series."))),
                DescribeRole.Theorem),
            Paragraph(Text("The full retained source energy recurrence and its scalar h/G exponential are established. "
                + "The regular charged-product scalar closed form, scalar shift-monomial factorization, "
                + "finite two-sheet coordinate composition, full Lambda/J normal-jet comparison on actual target tensors, "
                + "and both charged all-j ordinary-mode identities remain open. "
                + "There is no inference of a normalization defect. The original cocycle, chargeScalar, minus-charge monodromy, "
                + "mode shifts and unrestricted original carrier are unchanged. "
                + "The moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT objective remains open.")))));
}
