using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class OriginalSourceCoevaluationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit negative integer Gram inverse, occupation coefficient extractor and finite projected coevaluation on the full original fixed grades.",
        H("Original Source: Explicit Fixed Grade Coevaluation"),
        Blocks(
            Paragraph(Text("D is arbitrary LatticeGeneratingFieldLocality.LatticeData. Its actual oscillator is MvPolynomial (Fin D.rank x Nat) Complex and its actual Carrier is Charge(D) ->_0 Oscillator(D). Gc is the existing LatticeSugawaraCurrents.gramComplex D. A label a=(q,alpha) ranges over every charge and every finitely supported occupation; its energy is the existing integer chargeEnergy(D,q)+oscillatorEnergy(alpha). No rank24 or rootlessness premise is imposed. The fixed grade A_h is literally grade D h intersect fixedSpace D, for every integer h. Its full complex linear dual is a distinct type. This expression agrees with the separately owned MixedIntertwiner.fixedGrade, without importing or identifying its restricted dual with the source.")),
            Paragraph(Text("At oscillator mode k:Nat the physical integer frequency is s=k+1. Set A_k=-s Gc and B_k=(-s)^(-1) Gc^(-1), where the latter is the actual matrix nonsingular inverse. inverseOscillator is OriginalCurrentMetric.substitution B. With W_alpha=FactorialFockMetric.weight alpha=product_x alpha(x)!, define d_alpha=W_alpha^(-1) inverseOscillator(X^alpha) and d_(q,alpha)=Finsupp.single(-q,d_alpha). The empty factorial product is one. These definitions include off-diagonal Gram matrices, all occupations and opposite charges, including zero charge and rank zero.")),
            Definition("inverseOscillator", "Actual inverse substitution",
                "For every D, an algebra endomorphism of its original Oscillator, with variable image sum_j (-((k:Complex)+1))^(-1) Gc^(-1)[j,i] X_(j,k). The column convention is the existing variableImage convention; there is no guessed transpose or chosen inverse."),
            Definition("dualOscillatorMonomial", "Occupation dual polynomial",
                "For every D and alpha:Exponent D, multiply inverseOscillator D (monomial alpha 1) by the inverse of the existing complex occupation factorial W_alpha."),
            Definition("dualCarrierBasis", "Opposite charge dual vector",
                "For every D and a:Label D, the actual Carrier value single(-a.1,dualOscillatorMonomial D a.2), not a functional or an alternative Fock carrier."),
            Paragraph(Text("The original integerWick retunes SignedOscillatorWick.wick from frequency k+1/2 by integerScale(k)=(k+1)/(k+1/2). The existing substitution_comp and integerScale_mul_frequency give exactly integerWick(p,q)=F(substitution A p,q). The determinant-unit premise hu:IsUnit D.G.det is transported by the original complex_det_unit theorem. Thus A_k B_k=1, and substitution_inverse cancels substitution A after substitution B. The original factorial form gives F(X^alpha,p)=W_alpha p.coeff alpha; weight_pos cancels W_alpha. sourcePairing_single supplies the literal charge reversal and hence the actual coefficient extractor. No inverse, coevaluation, BPZ or crossing law is an assumption.")),
            Law("dualCarrierBasis_pairing", "Actual coefficient extraction",
                "For every D, hu:IsUnit D.G.det, a:Label D and v:Carrier D, sourcePairing D (dualCarrierBasis D a) v = carrierCoeffEquiv D v a. There is no homogeneity, fixedness or positivity premise on v."),
            Paragraph(Text("The existing substitution_monomial_weight applies directly to B: all monomials of the inverse polynomial have the same oscillatorEnergy as alpha. Scalar factorial normalization preserves this weight, and bilinear_neg_neg gives chargeEnergy(-q)=chargeEnergy(q). The existing mem_grade_iff then proves support at exactly the original energy, before any finite sum is formed. This argument does not need hu or real positive definiteness.")),
            Law("dualCarrierBasis_mem_grade", "Exact signed energy support",
                "For every D and a:Label D, dualCarrierBasis D a belongs to grade D (energy D a), with integer-valued energy and no extra assumptions."),
            Paragraph(Text("Let Pi be exactly the existing LatticeInvolution.plusPart D=(1+theta)/2. theta_single and sigma_monomial show that theta preserves every grade; theta_involutive puts Pi(v) in fixedSpace, and Pi(x)=x for fixed x. sourcePairing_theta gives Q(Pi(u),v)=Q(u,Pi(v)). Define e_a=Pi(carrierBasis D a) and c_a=Pi(dualCarrierBasis D a), both actual subtype values in A_h for a:EnergyFiber D h. The frame is redundant: no linear independence of projected vectors is asserted. In particular Q(c_a,x)=Q(d_a,x)=the actual coefficient x_a for x in A_h. This equality removes the second projection against a fixed input and preserves the original single half-average; it introduces no additional scalar 1/2 or orbit division.")),
            Definition("fixedFrame", "Projected source frame",
                "For every D, h:Int and a:EnergyFiber D h, e_a is plusPart D (carrierBasis D a.val), with proved membership in grade D h intersect fixedSpace D."),
            Definition("fixedDualFrame", "Projected inverse frame",
                "For every D, h:Int and a:EnergyFiber D h, c_a is plusPart D (dualCarrierBasis D a.val), with the same proved membership. It uses the existing source projector exactly."),
            Paragraph(Text("Only the finite representative requires hD:Matrix.PosDef (D.G.map (Int.cast:Int -> Real)). energyFiber_finite makes the entire actual EnergyFiber D h finite, including the negative and zero integer grades. The native coefficients give x=sum_a x_a b_a on every full grade; applying Pi gives x=sum_a x_a e_a on A_h. The implementation checks this expansion with the actual carrier coefficient equivalence. It does not replace the full fiber by a selected basis of projected orbits.")),
            Definition("representFixedGrade", "Prescribed finite inverse",
                "For every D, hD and h:Int, J_h:Module.Dual Complex A_h ->_l[Complex] A_h is the finite sum J_h(f)=sum_a f(e_a)c_a over the entire EnergyFiber D h. Finsum notation makes the value independent of a Fintype enumeration; finiteness is proved from hD, so no infinite junk sum is used."),
            Law("representFixedGrade_pairing", "Original Q representative",
                "For every D, hu:IsUnit D.G.det, hD:Matrix.PosDef(real G), h:Int, f:Module.Dual Complex A_h and x:A_h, sourcePairing D (representFixedGrade D hD h f).val x.val = f x. Expand the finite sum, use Q(c_a,x)=x_a, commute complex scalar factors, then apply f to the proved projected frame expansion."),
            Law("representFixedGrade_unique", "Uniqueness on the actual fixed grade",
                "With exactly D,hu,hD,h and f as above, for every x:A_h, if sourcePairing D x.val y.val=f y for all y:A_h, then x=representFixedGrade D hD h f. For a label of energy h, test the equality against its actual c_a and use symmetry and the coefficient extractor. Coefficients outside h vanish by exact grade membership. Injectivity of carrierCoeffEquiv concludes equality. Restricted nondegeneracy is a consequence, not an assumed theorem premise."),
            Law("fixed_contraction_comm", "Finite scalar pair exchange",
                "For every D,hu,hD,h and f,g:Module.Dual Complex A_h, sum_a f(e_a)g(c_a)=sum_a g(e_a)f(c_a). The left sum is g(J_h f)=Q(J_h g,J_h f), Q is symmetric, and the representative law gives f(J_h g), the right sum. No field mode is moved through Q."),
            Paragraph(Text("The full integer telescope retains negative grades and grade0 without a toNat conversion or a positive-grade restriction. Under hD, chargeEnergy_nonneg and nonnegative oscillator energy make negative fibers empty. energy_eq_zero_iff gives the unique label (0,0) at grade0; the inverse substitution fixes one, W_0=1 and theta fixes the vacuum, so the finite recipe there is f(vacuum) times vacuum. These boundary interpretations use the same recipe, rather than deleting the vacuum sector.")),
            Paragraph(Text("This is a classical explicit Wick inverse and finite-dimensional coevaluation construction, with no literature novelty claim. FactorialFockMetric and SignedOscillatorWick supply factorial normalization; OriginalCurrentMetric supplies matrix substitution; SourcePairingLaws and LatticeInvolution supply reflection and grading. The original owners expose the reused factorial form/monomial formula, half-frequency mode matrix, complex determinant transport and weighted monomial substitution. These visibility changes preserve their proof bodies and are supporting reuse, not additional scientific results. Mathlib finite-support, matrix inverse, weighted-homogeneous and finite-sum material retains its original authors and Apache-2.0 license.")),
            Paragraph(Text("The concrete consumer is P_k(u,v)=J_h(MixedIntertwiner.normalizedCoefficient D hu k u v at h), with h=H+K-k-1. The source-only module supplies the full grade-wise inverse required for this definition; the separately owned direct sum remains the restricted dual. The literal normalized-coefficient contraction and the tensor right action must be connected in their own implementation. Full arbitrary-source BPZ, J-action compatibility, the original analytic kernel and S/T comparisons, rational native-channel identification and the all-signed three-M identity remain separate obligations. This module proves no Monster realization, fusion, anomaly cancellation, CFT, string theory or AdS/CFT assertion."))
        ), []));

    private static DocumentBlock Law(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-source-coevaluation-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-source-coevaluation-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
