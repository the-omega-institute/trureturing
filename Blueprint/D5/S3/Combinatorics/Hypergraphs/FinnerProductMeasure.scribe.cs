using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypergraphs;

internal sealed class FinnerProductMeasureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/finner1992holder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fractional incidence budgets control products of local measurable factors " +
        "under one product probability law.",
        H("Finner's inequality on product probability spaces"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-coordinate-product-integral"),
                DeclarationHandle.Create(Prefix + "lintegral_fin_prod"),
                H("Product integrals of separate coordinate functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For any natural n, measurable spaces E_i indexed by Fin n, sigma-finite " +
                    "measures mu_i and measurable ENNReal functions a_i on E_i, the integral " +
                    "of product_i a_i(x_i) under Measure.pi(mu_i) equals the product of " +
                    "their separate integrals. No probability, positivity or finiteness " +
                    "of those integrals is required. The empty product is included. " +
                    "The proof uses the measure-preserving finite-Pi decomposition and " +
                    "binary Tonelli, including the ENNReal convention zero times infinity " +
                    "equal to zero. This same product-integral statement supports coordinate " +
                    "density products and the identification of normalized coordinate " +
                    "profiles by marginal integration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finner-marginal-estimate"),
                DeclarationHandle.Create(Prefix + "marginal_estimate"),
                H("Finner's estimate before all coordinates are integrated"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For any coordinate type I with decidable equality and finite row type J, " +
                    "take measurable ENNReal rows f_j supported on S_j under coordinate probability " +
                    "laws mu_i. Let nonnegative real weights satisfy the incidence budget at " +
                    "most one at every coordinate. For every finite coordinate set T, the " +
                    "T-marginal of the product of f_j^w_j is pointwise at most the product " +
                    "of the T-marginals of f_j raised to w_j. The ambient coordinate type " +
                    "need not be finite, and masses may be zero or infinite. This estimate " +
                    "is the coordinate induction used by the full inequality and supplies " +
                    "the saturation sandwich for deleted rows in its equality classification."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("finner-product-measure"),
                DeclarationHandle.Create(Prefix + "finner_product_measure"),
                H("Fractional hypergraph inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let I and J be arbitrary finite types. For each coordinate i in I, " +
                        "let X_i be a measurable space and mu_i a probability measure. Write " +
                        "mu=Measure.pi(mu_i) on the dependent product of the X_i. For every " +
                        "factor j in J choose a set S_j of coordinates, a measurable function " +
                        "f_j from the full product to ENNReal, and a real weight w_j>=0. " +
                        "DependsOn(f_j,S_j) means that f_j takes equal values on any two " +
                        "points agreeing at all coordinates in S_j. Assume that, for every i, " +
                        "the sum of w_j over j with i in S_j is at most one.")),
                    Paragraph(Text(
                        "Then the mu integral of the product over j of f_j(x) raised to w_j " +
                        "is at most the product over j of the mu integral of f_j, raised to " +
                        "w_j. Every integral uses this same product law, including the " +
                        "factor integrals on the right. There are no boundedness, finite " +
                        "alphabet, positive integral, disjoint support or global total-weight " +
                        "restrictions. Empty I, empty J and empty S_j are included. Values " +
                        "zero and infinity, zero weights, and their products use exactly " +
                        "ENNReal multiplication and real-power conventions, including " +
                        "zero times infinity equal to zero and any base to exponent zero " +
                        "equal to one.")),
                    Paragraph(Text(
                        "For a finite coordinate set T, integrate only those coordinates, " +
                        "using lmarginal(mu,T). The induction estimate bounds the marginal " +
                        "of the original product by the product of the individual marginals " +
                        "raised to their weights. At an added coordinate i, the induction " +
                        "hypothesis first bounds the integrand. Only factors with i in S_j " +
                        "can vary during this integration; every other marginal is constant " +
                        "in i because its original factor depends only on S_j. Split these " +
                        "two finite products, extract the constant product by the full " +
                        "measurable ENNReal lintegral_mul_const identity, and apply Holder " +
                        "to the varying factors. A constant-one factor with weight one minus " +
                        "the incidence sum absorbs unused budget. The marginal insertion " +
                        "identity gives the next induction estimate. At T=I, lmarginal_univ " +
                        "identifies every term with the integral under Measure.pi(mu_i).")),
                    Paragraph(Text(
                        "The proof directly reuses Mathlib's " +
                        "ENNReal.lintegral_mul_prod_norm_pow_le, Measurable.lmarginal, " +
                        "lmarginal_insert, lmarginal_update_of_mem, " +
                        "lmarginal_update_of_notMem, lmarginal_univ, and the measurable " +
                        "ENNReal real-power instance. The finite coordinate induction " +
                        "connects these suppliers to overlapping supports. The Library " +
                        "note identifies the classical theorem and distinguishes the " +
                        "directly read balanced finite-norm restatement from the " +
                        "probability weak-budget statement and extended endpoints proved " +
                        "here. No mathematical originality is claimed."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the equality target, take strictly positive real weights and require " +
                "each coordinate incidence sum to be exactly one. Require also that the " +
                "map i to M_i={j : i belongs to S_j} is injective and that each original " +
                "full-product mass m_j=integral_mu f_j is positive and finite. The target " +
                "is that equality in Finner holds if and only if there is one measurable " +
                "family h_i:X_i->ENNReal, with integral_mu_i h_i=1 for every i, such that " +
                "f_j=m_j times the product of those same h_i over S_j, mu-almost " +
                "everywhere for every j. Empty index types, empty supports, repeated " +
                "supports, zero values on sets of positive measure and infinity values " +
                "on null sets are included. The declaration " +
                "ProperSupportMarginalGluing.finner_equality_iff_common_profiles proves " +
                "this classification by induction on the active coordinate set.")),
            Paragraph(Text(
                "The directly read Bennett-Oh restatement in Section 1.1, after equation " +
                "(1.6), attributes to Finner a common-profile equality representation " +
                "g_j(P_j x)^{q_j}=c_j times the product of H_i(x_i) over S_j, with c_j>0. " +
                "For nonempty supports, balance and positive weights give w_j<=1, so " +
                "q_j=1/w_j lies in the stated finite range q_j>=1, including q_j=1. " +
                "A factor on an empty support is constant and equals m_j because the " +
                "full law is a probability measure. It contributes a scalar even when " +
                "its weight exceeds one. The Library note gives the support-space " +
                "correspondence and distinguishes this secondary attribution from " +
                "a proof of the ENNReal target.")),
            Paragraph(Text(
                "If a measurable common representation with positive finite c_j is " +
                "given, put a_i=integral_mu_i H_i. Tonelli gives m_j=c_j times the " +
                "product of a_i over S_j. Positive finite masses, together with " +
                "coordinate coverage from balance, force every a_i to be positive and " +
                "finite. Thus the same rescaling h_i=H_i/a_i in every incident row " +
                "gives unit integrals and replaces each row coefficient by exactly " +
                "m_j. This normalization preserves common profiles and does not " +
                "assume positive conditional slice masses.")),
            Paragraph(Text(
                "The support-intersection bridge uses the same actual product law. " +
                "If f and g agree almost everywhere, f depends on S, and g is " +
                "measurable and depends on T, integrate g over the complement of S. " +
                "The resulting measurable function depends on S intersect T and " +
                "represents f almost everywhere: the corresponding marginal of f " +
                "is pointwise f, and Fubini transports the original equality to " +
                "almost every slice. No positivity or finite integral is needed " +
                "for this bridge. For a fixed i, the intersection of S_j over all " +
                "j in M_i is exactly {i}, by balance, positive weights and incidence " +
                "injectivity. Applying the bridge to conditional profiles still " +
                "requires their almost-everywhere equality under one common product " +
                "law and recovery of every original factor across zero marginals.")),
            Paragraph(Text(
                "An explicit candidate chooses one j(i) in M_i and an anchor a in " +
                "the full product, then sets h_i(t)=m_{j(i)}^{-1} times the marginal " +
                "of f_{j(i)} over every coordinate other than i, evaluated at a " +
                "with coordinate i replaced by t. These are measurable functions. " +
                "Marginal insertion and full-product integration give each integral " +
                "equal to one, using the positive finite original mass. The equality " +
                "theorem in ProperSupportMarginalGluing constructs a common family " +
                "by active-set induction and proper-support marginal gluing. Identifying " +
                "every resulting profile with this particular anchored candidate is " +
                "a separate canonical-choice correspondence question.")),
            Paragraph(Text(
                "For the converse implication, the finite intersection of the rowwise " +
                "full-measure sets permits substitution of every representation in the " +
                "powered product. Distribute the positive real powers over finite " +
                "ENNReal products and interchange the factor and coordinate products. " +
                "For each coordinate, the incident powers sum to one, leaving " +
                "(product_j m_j^{w_j}) times product_i h_i(x_i). Integrating the " +
                "coordinate product gives the product of its unit integrals. This " +
                "argument retains the ENNReal zero/infinity convention and uses no " +
                "pointwise cancellation. If I is empty, all supports are empty and " +
                "the assertion reduces to constant-mass identities; if J is empty " +
                "and I is nonempty, balance is inconsistent; if both are empty, " +
                "all products and the integral equal one.")))));
}
