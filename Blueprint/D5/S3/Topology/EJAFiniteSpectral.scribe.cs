using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class EJAFiniteSpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every element of a general finite real Euclidean Jordan algebra has a complete finite spectral resolution on its original carrier, using its given positive definite associative inner product and no JB norm assumption.",
        H("Finite spectra in a general real Euclidean Jordan algebra"),
        Blocks(
            Describe.Remark(DescribeId.Create("scalar-compatibility"),
                H("Scalar compatibility of the commutative product"),
                F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Open, F.Id("J"), F.Colon, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Type")), F.Close, F.Comma, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("NonUnitalNonAssocCommRing")),
                    F.Sp, F.Id("J"), F.CloseBracket, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("Module")), F.Sp,
                    F.Mathbb, F.Grp(F.Id("R")), F.Sp, F.Id("J"), F.CloseBracket, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("IsScalarTower")), F.Sp,
                    F.Mathbb, F.Grp(F.Id("R")), F.Sp, F.Id("J"), F.Sp, F.Id("J"),
                    F.CloseBracket, F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Open, F.Id("r"), F.Colon, F.Sp,
                    F.Mathbb, F.Grp(F.Id("R")), F.Close, F.Sp,
                    F.Open, F.Id("a"), F.Sp, F.Id("b"), F.Colon, F.Sp, F.Id("J"),
                    F.Close, F.Comma, F.Sp,
                    F.Id("a"), F.Sp, F.Circ, F.Sp, F.Open,
                    F.Id("r"), F.Sp, F.Cdot, F.Sp, F.Id("b"), F.Close,
                    F.Sp, F.Eq, F.Sp, F.Open,
                    F.Id("r"), F.Sp, F.Cdot, F.Sp, F.Open,
                    F.Id("a"), F.Sp, F.Circ, F.Sp, F.Id("b"), F.Close, F.Close)),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here the circle denotes the multiplication of the arbitrary nonunital nonassociative commutative ring J, and the dot denotes its real scalar action. The public Lean theorem `mul_smul_comm'` proves the identity from exactly the displayed ring, module and scalar-tower instances; no Jordan law is needed. This makes multiplication by a fixed element real linear and supplies the scalar compatibility used in polynomial evaluation and the spectral-norm Peirce projections.")))),
            Describe.Lean(DescribeId.Create("formal-reality"),
                DeclarationHandle.Create("D5/S3/Topology/EJAFiniteSpectral.IsFormallyReal"),
                H("The auxiliary formal-reality predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Formal reality means that a vanishing finite sum of Jordan squares has every underlying element zero. This auxiliary property is derived from the given positive definite associative inner product and unit inside the spectral proof. It is not a premise of the public EJA spectral theorem."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("genuine-eja-data"),
                DeclarationHandle.Create("D5/S3/Topology/EJAFiniteSpectral.Data"),
                H("The original Euclidean Jordan data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original real inner-product space X carries a specified real bilinear product S and a unit u. Data requires symmetry, the unit law, the ordinary Jordan identity and associativity of the given positive definite inner product. Finite dimensionality is a separate theorem hypothesis. No spectral data, six-law JB norm, cone selfduality, primitive frame, simplicity, matrix representation, specialness or classification is assumed. Nonisomorphic direct sums and the Albert case are within this interface whenever they carry these genuine laws."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("general-eja-finite-spectral-resolution"),
                DeclarationHandle.Create("D5/S3/Topology/EJAFiniteSpectral.finite_spectral_resolution"),
                H("Complete spectral resolution on X"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every actual a the theorem constructs n, original elements e_i and real numbers r_i. Each e_i is idempotent; different e_i multiply to zero; their sum is u; the r-weighted sum is a; the r-squared-weighted sum is S(a,a). If u is zero the construction uses n equal to zero. Scalar elements, repeated spectral values and the zero spectral value are covered. Idempotents are allowed to be zero and are not asserted primitive.")),
                    Paragraph(Text("Pairing a sum of squares with the original unit converts it to a sum of nonnegative squared inner-product lengths. Positive definiteness therefore proves formal reality; it is not an additional premise. The algebraic spectral proof uses the polarized Jordan identity and induction on total power degree to prove power associativity. The annihilating ideal of the positive powers is nonzero by finite dimensionality. Formal reality rules out nilpotents, makes its generator squarefree, excludes a zero constant term and excludes non-real complex roots. Lagrange polynomials at the distinct real roots together with zero yield actual idempotents in X. Adding the complementary idempotent with coefficient zero makes the family complete. Bilinearity and the proved pairwise orthogonality reconstruct S(a,a). No eigenvalues of multiplication on the whole ambient X are identified with the Jordan spectrum.")),
                    Paragraph(Text("This is an adapted port of the live spectral proof from Bryan Ehrlich's ehrlich-b/euclidean-jordan at immutable revision a83407e4dbf73c77c31a2291c02f20b37a5ebbaf: Power, PowerAssoc, FormallyReal, Subalgebra, Frame, Spectral and the inner-product formal-reality argument in Class. The upstream spectral_resolution_complete and spectral_resolution_bilinear supply the spectral construction. Its v4.33.0 toolchain and mathlib db584cd6d46c92f209a44c0f1c829460d327499d differ from this repository's pins, so it is ported rather than added as a dependency. The Apache-2.0 license is retained at docs/reports/third-party/euclidean-jordan-LICENSE.txt. Only live proof dependencies are retained; unrelated Peirce and matrix interfaces are excluded. The upstream polarized identity is replaced by the directly applicable pinned Mathlib identity two_nsmul_lie_lmul_lmul_add_add_eq_zero. Retire the port when this repository's pinned Mathlib contains an equivalent general bilinear spectral theorem and use that theorem directly.")),
                    Paragraph(Text("Repository reuse boundary: JBAlgebra's npow, polarized and private powers_structure already establish the algebraic induction under six-law JBAlgebra.Data. Their statements require product_norm, square_norm and square_mono, so they cannot be applied to these weaker EJA data without first proving the missing norm realization. JBFiniteSpectral likewise uses those stronger norm laws in the generated algebra, complexification and Gelfand separation. Those sources remain independent valid suppliers; no specialization between the two interfaces is retained. The present classical port pays the actual weaker-hypothesis spectral gap and makes no mathematical novelty claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source application: Quantum Origin V 75.4(I), before equation 75.12, requires a complete spectral resolution in a general finite EJA. This theorem supplies exactly that predecessor from the original carrier, product, unit and given inner product. The spectral norm and square-defect consumers are supplied separately by EJASpectralNorm and EJADefiniteDomain. For the spectral identities alone, no normalization of the inner product to the canonical trace is needed.")),
            Paragraph(Text("EJASpectralNorm supplies the spectral JB norm and its laws on a separate type copy. EJADefiniteDomain supplies the original-carrier positive-map square defect, full mixed identities and the Jordan-generating definite-domain consumer. Canonical trace normalization, inner-product cone selfduality, primitive-frame refinement, weight-commutant closure, support normalization and the full J/H/PRE and H13/C13 interfaces remain separate source bridges.")),
            Paragraph(Text("The new Reg mirror reconstructs the complete EJA telescope and actual product readout. Whole-family intervention, sensitivity, observational dependence and compiled source-coordinate ties remain separate audit obligations; no declared_validated registration is asserted.")))));
}
