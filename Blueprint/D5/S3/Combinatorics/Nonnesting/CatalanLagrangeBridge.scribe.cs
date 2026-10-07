using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class CatalanLagrangeBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.";
    private const string Supplier = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient";
    private static readonly LibraryNoteRef Lagrange = LibraryNoteRef.Create("D5/L/PermutationPatterns/gessel2016lagrange");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Catalan root supplies a formal substitution inverse used to recover the actual P13 series and transforms arbitrary rational-series coefficients through the original owner’s public Lagrange supplier.",
        H("Catalan Root and Lagrange Coefficient Transform"),
        Blocks(
            Paragraph(Text("Let C be the rational image of Mathlib’s Catalan series and q = C − 1. These statements concern formal power series. The public coefficient supplier is "), Ref(Supplier), Text("; its proof remains in the original nonnesting enumeration owner, where result also uses it.")),
            Paragraph(Text("The classical lineage is Gessel’s Lagrange inversion survey, Theorem 2.1.1 and Section 2.3. The proofs here combine that supplier with Mathlib’s Catalan equation, substitution, inverse, order and polynomial coefficient APIs. The coefficient transform retains n ≥ 1 and the positive-power bridge retains 1 ≤ k ≤ n.")),
            Node("catalan-lagrange-ps", "Rational formal power series", "PS",
                "PS abbreviates PowerSeries ℚ. All series, coefficients and cancellations in this module are formal and rational; no analytic convergence hypothesis is used.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-catalanunit", "The rational Catalan series", "catalanUnit",
                "C is the image of Mathlib’s natural-coefficient Catalan series under Nat.castRingHom ℚ. Its coefficient at index n is the rational cast of the nth Catalan number.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q", "The zero-constant Catalan root", "q",
                "The series q is C − 1. This is the root substitution used in Gessel’s Section 2.3, with its constant coefficient removed.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-catalanunit-equation", "The Catalan equation over ℚ", "catalanUnit_equation",
                "C²X + 1 = C follows by mapping Mathlib’s catalanSeries_sq_mul_X_add_one to rational coefficients.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-catalanunit-constantcoeff", "Constant coefficient of C", "catalanUnit_constantCoeff",
                "The constant coefficient of the rational Catalan series C is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q-constantcoeff", "Admissibility of the root substitution", "q_constantCoeff",
                "The constant coefficient of q is zero. The substitution proofs use this equality to construct HasSubst q; admissibility is not assumed for an arbitrary nonzero-constant series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q-equation", "The Catalan root equation", "q_equation",
                "The series q satisfies q = X(1 + q)², the Catalan instance of the Lagrange fixed-point equation.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Lagrange)),
            Node("catalan-lagrange-sourceunitsq", "The square unit", "sourceUnitSq",
                "sourceUnitSq is (1 + X)² in ℚ⟦X⟧.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-sourceunitsqinv", "The formal multiplicative inverse", "sourceUnitSqInv",
                "sourceUnitSqInv is PowerSeries.invOfUnit applied to (1 + X)² with the unit Units.mk0 (1 : ℚ) one_ne_zero. This is a formal unit inverse, not a numerical division or an analytic reciprocal.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-zeta", "The inverse substitution", "zeta",
                "The series ζ is X times sourceUnitSqInv, so it represents X/(1 + X)² as a formal power series.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-sourceunitsq-inv-right", "Right multiplicative inverse", "sourceUnitSq_inv_right",
                "sourceUnitSq times sourceUnitSqInv equals one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-sourceunitsq-inv-left", "Left multiplicative inverse", "sourceUnitSq_inv_left",
                "sourceUnitSqInv times sourceUnitSq equals one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-zeta-constantcoeff", "Admissibility of the inverse substitution", "zeta_constantCoeff",
                "The constant coefficient of ζ is zero, supplying HasSubst ζ for lawful composition in the actual carrier recovery.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-zeta-subst-q", "Substituting q into ζ", "zeta_subst_q",
                "PowerSeries.subst q ζ = X. In dot notation this is ζ.subst q = X: q is the inner substitution argument. The proof substitutes into the square-unit identity and uses q = X(1 + q)².", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Lagrange)),
            Node("catalan-lagrange-catalanfactor", "The Lagrange factor", "catalanFactor",
                "catalanFactor is the formal series (1 + X)² used as the factor in the public generic Lagrange theorem.", DescribeRole.Definition, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q-factor-equation", "The supplier’s fixed-point hypothesis", "q_factor_equation",
                "q = X times PowerSeries.subst q catalanFactor. Together with q_constantCoeff this discharges the two series hypotheses of the original owner’s lagrange_coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-binomialcoefficient", "Coefficients of the square-factor powers", "binomialCoefficient",
                "For natural exponent e and index j, the coefficient of Xʲ in (1 + X)ᵉ is the rational cast of e.choose j. The proof reuses the polynomial coefficient formula.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-one-sub-x-power-coefficient", "A binomial difference", "one_sub_X_power_coefficient",
                "For natural e and j, the coefficient of Xʲ in (1 − X)(1 + X)ᵉ is one if j = 0, and otherwise equals the rational cast of e.choose j minus the rational cast of e.choose (j − 1). The zero-index case is explicit; natural subtraction is not silently replaced by integer subtraction.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q-power-coefficient-bridge", "Positive powers of the Catalan root", "q_power_coefficient_bridge",
                "For natural n and k with 1 ≤ k ≤ n, the coefficient of Xⁿ in qᵏ equals the coefficient of Xⁿ⁻ᵏ in (1 − X)(1 + X)^(2n − 1). The proof directly invokes the original owner’s public lagrange_coefficient, then uses Pascal’s identity and a binomial ratio. It treats k = n separately and cancels the rational cast of n only after proving it nonzero.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Lagrange)),
            Node("catalan-lagrange-q-zero-power-coefficient-bridge", "The zero-power case", "q_zero_power_coefficient_bridge",
                "For n ≥ 1, the coefficient of Xⁿ in q⁰ equals the coefficient of Xⁿ in (1 − X)(1 + X)^(2n − 1). Both vanish; the binomial symmetry argument supplies this case separately from the positive-power supplier.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Lagrange)),
            Node("catalan-lagrange-q-subst-coefficient-transform", "An arbitrary-series coefficient transform", "q_subst_coefficient_transform",
                "For every G : ℚ⟦X⟧ and natural n ≥ 1, coeff n (G.subst q) = coeff n ((1 − X)(1 + X)^(2n − 1)G). This is Gessel’s equation (2.1.2) specialized to R(t) = (1 + t)². The proof uses HasSubst q, the order bound that kills powers beyond n, a finite coefficient sum, and the separate k = 0 and 1 ≤ k ≤ n bridges. No restriction to polynomial G is imposed.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Lagrange)),
            Paragraph(Text("The actual P13Enumeration consumer uses ζ.subst q = X on the recovery path and applies the arbitrary-series coefficient transform to the explicit scalar G. The matching identification and actual boundary elimination belong to that consumer. This bridge retains the inverse direction used there; the unused reverse companion is omitted."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo"))
        ]));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
