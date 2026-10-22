using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockRegularChargedScalarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula Lattice => F.Id("D");
    private static Formula First => F.Id("a");
    private static Formula Second => F.Id("b");
    private static Formula Gram => Call("bilinear", Lattice, First, Second);
    private static Formula AbsoluteGram => Call("natAbs", Gram);
    private static Formula Start => Call("toNat", Call("add", AbsoluteGram, Gram));
    private static Formula Gaussian => Call("chargedEnergyGaussian", Lattice, First, Second);
    private static Formula Cocycle => Call("epsilon", Lattice, First, Second);
    private static Formula Constant(Formula value) => Call("C", value);
    private static Formula Product(Formula left, Formula right) => Call("mul", left, right);
    private static Formula Scalar(Formula charge) => Call("chargeScalar", Lattice, charge);
    private static Formula ForCharges(Formula body) => Seq(
        Forall, Sp, Lattice, InMacro, Sp, Call("LatticeData"), Comma, Sp,
        Forall, Sp, First, Comma, Second, InMacro, Sp, Call("Charge", Lattice), Comma, Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original charged exponential under the formal two-sheet substitution", H("Original Charged Scalar"), Blocks(
            Paragraph(Text("D is the unrestricted original lattice datum; a,b are arbitrary integral charges. "
                + "A is the literal chargeNorm(D,a), and g is the signed original bilinear(D,a,b). "
                + "G is the existing chargedEnergyGaussian, defined from the original singleton and pair logarithm. "
                + "The preceding retained-source theorem identifies its coefficients with actualEnergyScalar. "
                + "No positivity or rank assumption is introduced, and scalar evaluation is not a vacuum expectation.")),
            Describe.Lean(DescribeId.Create("actual-charged-scalar-two-sheet"),
                DeclarationHandle.Create(Prefix + "actual_charged_scalar_two_sheet"), H("Actual Exponential Scalar"),
                StatementSource.FromAuthor(Disp(ForCharges(Seq(
                    Call("sheetSubstitution", Gaussian), Eq,
                    Call("regularScalarOnSheet", Lattice, First, Second))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "G(T(u))=(1-u)^(A+2g)(1+u)^(-A), with both integer powers interpreted by the literal "
                    + "Mathlib binomial series. The proof derives the logarithmic differential law from the actual "
                    + "original energy coefficients, composes with the proved formal coordinate and original root, "
                    + "and identifies the two exponential solutions using the genuine initial coefficient one. "
                    + "It does not assume the desired regular scalar identity or recurrence. "
                    + "The full normal-polynomial Lambda/J comparison, product recurrence, and both unchanged "
                    + "plus/minus all-j endpoints on arbitrary original target tensors remain open. "
                    + "The moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT goal remains active/open."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-regular-charged-scalar-ratio"),
                DeclarationHandle.Create(Prefix + "actual_regular_charged_scalar_ratio"), H("Original Regular Scalar Ratio"),
                StatementSource.FromAuthor(Disp(ForCharges(Seq(
                    Product(Constant(Product(Product(Scalar(First), Scalar(Second)), Cocycle)),
                        Call("eval", Call("clearedPolynomial", Gram), Call("halfRoot"))),
                    Eq,
                    Product(Product(Product(
                        Constant(Product(Scalar(Call("add", First, Second)), Cocycle)),
                        Call("pow", F.Id("X"), Start)), Gaussian),
                        Call("halfLabel", Call("sub", Call("chargeNorm", Lattice, First),
                            Product(F.D(2), AbsoluteGram)))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Let N=natAbs(g), r=(N+g).toNat, q=(1+t)^(-1/2), and E=A-2N. "
                    + "The theorem identifies chargeScalar(a) chargeScalar(b) epsilon(a,b) P_g(q) "
                    + "with chargeScalar(a+b) epsilon(a,b) t^r G(t) (1+t)^(E/2). "
                    + "Here eval(P,q) is exactly Polynomial.eval2(C,q,P), C embeds a scalar as a constant "
                    + "power series, and X is the formal generator t. The displayed mul, add, sub, pow and inv "
                    + "have their ordinary algebraic meanings, with natAbs and toNat exactly as in Lean. "
                    + "P_g is the unchanged original clearedPolynomial, and the half-label coefficients remain "
                    + "literal choose(E/2,n). The original cocycle appears exactly once on each side. "
                    + "The exponential closed form is derived from its actual logarithmic coefficients; no desired "
                    + "normalization identity is an extra hypothesis. The formal coordinate has unit linear "
                    + "coefficient four, so its formal substitution inverse pulls the identity back to t. "
                    + "Both signs of g and arbitrary integral charges are included. No positivity, rank, "
                    + "finite-charge cutoff, or target-vacuum premise is introduced. "
                    + "The norm-addition and chargeScalar normalization helpers adapt the sealed "
                    + "LatticeHalfFockLiteralChargedLeading.norm_add and scalar_normalization proofs and "
                    + "reuse LatticeActualGeneratorLocality.bilinear_add_right from LatticeActualProductKernel. "
                    + "Those suppliers are inherited normalization, not new mathematical credit. "
                    + "The new scalar comparison does not yet prove the all-label Lambda/J normal-polynomial "
                    + "comparison, the actual product recurrence or either unchanged all-j endpoint. "
                    + "Actual kernel validation does not certify complete registration or remote admission."))),
                DescribeRole.Theorem))));
}
