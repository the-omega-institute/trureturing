using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOrderedProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported ordered native half-Fock products", H("Native Product Expansions"), Blocks(
            Paragraph(Text("For arbitrary D,a,b,p and integers k,l, write q_a=B(a,a), "
                + "R_a[k]=oscillatorCoefficient D a (k-q_a), and h_g[r]=coeff_r(halfContraction D a b), g=B(a,b). "
                + "R is notation for the delivered native endomorphism, not a replacement implementation. "
                + "half_creation_coefficient_transport supplies the exact translated creation coefficient. "
                + "The bivariate common kernel supplies finite supports before sums are distributed. "
                + "Polynomial induction uses the native oscillator creator recurrence and both independent kernel shifts.")),
            Describe.Lean(DescribeId.Create("native-first-ordered-product"),
                DeclarationHandle.Create(Prefix + "native_ordered_product"), H("First ordered product"),
                StatementSource.FromAuthor(Disp(Call("FirstOrderedProduct", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("k"), F.Id("l"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly R_a[k](R_b[l]p)=sum_(r>=0) h_g[r] J_ab[k+r,l-r](p). "
                    + "The sum is statewise finite on every arbitrary polynomial p. No sign restriction on g, "
                    + "occupation cutoff, analytic BCH identity, or unproved infinite operator rearrangement is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-reverse-ordered-product"),
                DeclarationHandle.Create(Prefix + "native_reverse_ordered_product"), H("Reverse ordered product"),
                StatementSource.FromAuthor(Disp(Call("ReverseOrderedProduct", F.Id("D"), F.Id("a"), F.Id("b"), F.Id("k"), F.Id("l"), F.Id("p")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly R_b[l](R_a[k]p)=sum_(r>=0) h_g[r] J_ab[k-r,l+r](p). "
                    + "Exchange of the actual kernel and symmetry of the actual bilinear form identify this with the "
                    + "first ordered theorem with charges and coefficient indices exchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-tensor-first-product"),
                DeclarationHandle.Create(Prefix + "charged_tensor_ordered_product"), H("First product on every actual tensor state"),
                StatementSource.FromAuthor(Disp(Call("TensorFirstProduct", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b"), F.Id("e"), F.Id("f"), F.Id("state")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every D,hu,a,b,e,f,state, A_a[e](A_b[f]state)=c_a c_b sum_r h_g[r] "
                    + "TensorProduct.map(J_ab[e+q_a+r,f+q_b-r],U_a U_b)state. Actual tensor induction "
                    + "proves rectangular bounds and pointwise finite support before the sum defines a linear readout. "
                    + "The pure-tensor formula follows directly from the delivered native oscillator product; "
                    + "addition extends it to all unrestricted ActualTensor states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-tensor-reverse-product"),
                DeclarationHandle.Create(Prefix + "charged_tensor_reverse_ordered_product"), H("Reverse product on every actual tensor state"),
                StatementSource.FromAuthor(Disp(Call("TensorReverseProduct", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b"), F.Id("e"), F.Id("f"), F.Id("state")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every D,hu,a,b,e,f,state, A_b[f](A_a[e]state)=c_a c_b sum_r h_g[r] "
                    + "TensorProduct.map(J_ba[f+q_b+r,e+q_a-r],U_b U_a)state. Native branch exchange "
                    + "identifies that oscillator kernel with J_ab[e+q_a-r,f+q_b+r]. The actual ground action "
                    + "retains its reversed order; it is not silently replaced by U_a U_b."))), DescribeRole.Theorem),
            Paragraph(Text("For the actual tensor fields, hu:IsUnit D.G.det selects groundRank, groundRepresentation and "
                + "groundAction from actual_twisted_ground_representation D hu. chargedCoefficient(a,e) is "
                + "c_a times TensorProduct.map(oscillatorCoefficient(a,e),groundAction(a)), c_a=2^(-q_a). "
                + "Consequently the unshifted first index is k=e+q_a, the second is l=f+q_b, "
                + "and the ordered ground action is U_a U_b, not an assumed commuting action.")),
            Paragraph(Text("Physical coordinates are z=x^2,w=y^2. The physical locality certificate still requires the "
                + "actual finite j=0..abs(g) binomial commutator sum with indices e-2(N-j),f-2j. "
                + "Both cover factors 1-s and 1+s must be cleared: m=(-g).toNat,n=g.toNat and "
                + "(1-s)^m(1+s)^n h_g=(1-s)^n(1+s)^m. Positive g retains an opposite-sheet pole. "
                + "Rational-function equality is not equality of the two unregularized iota expansions. "
                + "Physical coefficient locality, twisted Jacobi, physical derivatives shifting cover exponents by two, "
                + "all-order ordinary-field iterates and orbifold intertwiners remain separate proof obligations. "
                + "Scalar c_a matches leading physical iterate normalization; locality alone does not determine it. "
                + "Classical provenance, zero novelty claim; no full Leech, Monster, fusion, string or AdS realization follows.")))));
}
