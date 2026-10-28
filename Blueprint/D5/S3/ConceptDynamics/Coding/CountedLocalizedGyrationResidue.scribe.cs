using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedLocalizedGyrationResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CountedLocalizedGyrationResidue",
        H("Signed congruence for the fixed positive-lift cochain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("existing-six-countedlocalizedgyrationresidue-dyadicgyration-nonnegative"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration_nonnegative"),
                H("The dyadic cochain recovers the actual forward residue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonzero period divisible by three, cast the nonnegative rectangular factors through the integers into the dyadic ring. Their dyadic gyration equals the reduction of the original ranked relative forward gyration. This is the bridge used by the relabel, positive-word and presentation-time comparisons."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedlocalizedgyrationresidue-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_signed_agreement"),
                H("Signed congruence for the fixed positive-lift cochain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a commutative ring L equipped with reduction rho to ZMod of three to the power e plus one, each matrix entry is lifted to its natural residue plus that modulus. The canonical cochain is the same signed integer gyration polynomial evaluated at these strictly positive representatives, reduced modulo three. Here e is at least the three-adic valuation of the factorial of twice the period. Any signed integer pair with the same reductions gives the same value, by the explicit accepted integral numerator and the clearing-denominator theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedlocalizedgyrationresidue-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.canonicalLocalizedGyration_triangle"),
                H("One rectangular family satisfies the triangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Lift R, U and V separately. Products of their lifts have the correct reductions because rho and integer reduction are ring homomorphisms. Signed agreement compares the cochain on each product with its integer value even when an intermediate dimension vanishes. The nonnegative integer triangle then yields the rectangular localized triangle. The construction is uniform over all dimensions, including zero, and every nonzero period divisible by three."))),
                DescribeRole.Theorem),
            Paragraph(Text("Agreement with actual primitive-path forward gyration.")),
            Paragraph(Text("Let n and m be arbitrary natural dimensions, d a nonzero period with three dividing d (write hd for this divisibility), L any commutative ring, e a natural exponent at least the three-adic valuation of (2*d)!, and rho a ring homomorphism from L to ZMod of three to the power e plus one. For arbitrary natural counted matrices R of size n by m and S of size m by n, map their entries first to the integers and then to L. The canonicalLocalizedGyration value of this pair equals ZMod.castHom hd (ZMod 3) applied to relativeForwardGyration R S. Zero entries, empty dimensions and singular matrices remain allowed; no inverse or determinant condition is used.")),
            Paragraph(Text("Apply canonicalLocalizedGyration_signed_agreement to those matrices in L and the signed integer pair R.map (Nat.castRingHom ℤ), S.map (Nat.castRingHom ℤ). Entrywise map_intCast for rho supplies both reduction equalities, including zero entries. The accepted relativeForwardGyration_eq_order_types at Sum.elim of the R and S entries identifies the actual primitive-path offset sum with the natural orderTypeGyrationLift in ZMod d. Mapping to ZMod 3 commutes with the integer cast because three divides d. Finally Sum.elim of the integer-cast entries is the pointwise cast of the natural tuple; unfolding integerGyrationValue and using Ring.choose_natCast and Nat.cast_prod identifies signedGyrationLift with orderTypeGyrationLift. This derives the agreement for the same invariant and the full stated parameter range.")),
            Describe.Lean(
                DescribeId.Create("countedlocalizedgyrationresidue-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue.dyadicGyration"),
                H("The fixed dyadic specialization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The canonical dyadic value uses the universal localization reduction at the three-adic valuation of the factorial of twice the period. Signed agreement and the rectangular triangle apply to this same specialization. The preceding derivation also identifies its nonnegative integer inputs with actual orbit gyration. The localization's integer embedding agrees with the embedding induced by its ring structure, by uniqueness of ring homomorphisms from the integers. No separate period or square wrapper is needed. These arguments use classical integer-valued polynomial congruences and localization; they assert no novelty, full mod-six law, image exhaustion, or original-h SGCC completion."))),
                DescribeRole.Definition))));
}
