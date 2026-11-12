using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class JBSquareDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unital maps positive on squares into a complete real six-law JB algebra are multiplicative when they preserve idempotence on a real spanning set, provided the original source product has finite spectral resolutions.",
        H("Square defects and spanning idempotents"),
        Blocks(
            Paragraph(Text("The source X is a real module with a specified symmetric bilinear product S and specified unit u. The target Y is a complete real normed space with the specified product T, unit v and the genuine six JB laws Data(Y,T,v). The same real linear map Phi sends u to v and sends every source square to an actual square in Y. No associative, special, complex-matrix or completely positive representation is used.")),
            Describe.Lean(DescribeId.Create("finite-spectral-resolutions"),
                DeclarationHandle.Create("D5/S3/Topology/JBSquareDefect.HasFiniteSpectralResolutions"),
                H("The explicit spectral supplier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real source element a there is a finite family of original idempotents e and real coefficients r whose sums are u, a and S(a,a) with coefficients 1, r and r squared. This predicate contains no target map, square-defect condition or multiplicativity conclusion. Its existence for the original finite EJA is an additional unproved application bridge; this module does not manufacture that existence from a certificate field called EJA."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spectral-defect-sum-identity"),
                DeclarationHandle.Create("D5/S3/Topology/JBSquareDefect.square_defect_identity"),
                H("The explicit same-spectrum sum identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For the same complete spectrum, target product and unital map, the sum of the quadratic representations at r_i v-Phi(a) applied to Phi(e_i) is exactly the square defect. This is the algebraic identity used by square_defect_of_spectral. It requires only the symmetric target product and unit law, with no JB norm assumption and no positivity of r_i v-Phi(a)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-square-defect-cross"),
                DeclarationHandle.Create("D5/S3/Topology/JBSquareDefect.zero_defect_cross"),
                H("Zero defect gives every mixed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("If all square defects have actual square roots and the defect at a vanishes, all real cross products with a are preserved. Signed perturbations, square monotonicity and a uniform bound force the cross defect to vanish. The source product is assumed symmetric; no associativity or representation is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-square-defect"),
                DeclarationHandle.Create("D5/S3/Topology/JBSquareDefect.square_defect_of_spectral"),
                H("The square defect is an actual square"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every a, Phi(S(a,a))-T(Phi(a),Phi(a)) has a square root in the same Y. In a finite spectral resolution put z_i=Phi(e_i) and b=Phi(a). The defect is the sum of U(r_i v-b,z_i). The existing JBComplexification.quadratic_preserves_squares supplies positivity for every real argument r_i v-b, without a sign assumption on it. Finite sums are actual squares by the existing norm-center characterization and the norm triangle inequality. This result is used in the spanning-idempotent theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spanning-idempotents-multiplicative"),
                DeclarationHandle.Create("D5/S3/Topology/JBSquareDefect.multiplicative_of_spanning_idempotents"),
                H("All cross products are forced by a spanning set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real spanning subset s of X, if each e in s and Phi(e) are idempotent in their respective original products, then Phi(S(a,x))=T(Phi(a),Phi(x)) for every real a,x. The square-defect result first supplies all perturbed defects as actual squares. If the defect at a vanishes, the defects at t a+x and -t a+x sum to twice the defect at x and differ by four t times the cross defect. Square monotonicity bounds both perturbed defects uniformly in t. An explicit real t contradicts any nonzero cross defect. Linear span induction then proves the whole product identity. Zero images, empty spectral index types and degenerate carriers are permitted."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application boundary for Quantum Origin V Section 74.2. This proves the square-defect and subsequent linear-extension step under the displayed suppliers. The intended source product and map are unchanged. Applying the result to the actual normalized maps of Section 74 still requires the faithful PRE-to-EJA/JB bridge and finite spectral resolutions, U and G interior before normalization, actual support normalization of each chosen frame image, and the weight commutator. The first and second original interfaces, the product-frame spanning argument and the original same-rho H13/C13 consumer are not supplied here. In particular neither Theorem 74.7 nor 74.9 nor the queued 73.7 is declared proved. This module provides no freeze or atom coverage.")))));
}
