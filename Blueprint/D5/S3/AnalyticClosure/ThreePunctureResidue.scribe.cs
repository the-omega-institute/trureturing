using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class ThreePunctureResidueDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/AnalyticClosure/ThreePunctureResidue";
    private const string Prefix = Gid + ".";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, "Three-puncture residue balance and its two coordinate changes.",
            "evidence-not-specified-by-formal-manifest"),
        H("Residues at zero, one and infinity"),
        Blocks(
            D("three-puncture-principal-part", "principalPart", "Finite principal part",
                DescribeRole.Definition,
                Text("The length-n principal part at a is the sum of cⱼ(z − a)^(−j−1) "
                    + "for 0 ≤ j < n, indexed from the simple pole.")),
            D("three-puncture-simple-coefficient", "simpleCoeff", "Simple-pole coefficient",
                DescribeRole.Definition,
                Text("The coefficient of (z − a)⁻¹ is c₀ for a nonempty principal part and "
                    + "zero for the empty part.")),
            T("three-puncture-inverse-remainder", "deriv_inverse_remainder",
                "The linear term of the inverse-coordinate remainder",
                Text("Let G be holomorphic off zero and one and have finite principal parts with "
                    + "analytic remainders at zero, one and in the scalar germ G(u⁻¹) at u = 0. "
                    + "Subtract the two finite principal parts and the polynomial in z determined "
                    + "by the inverse-coordinate principal part. The remainder extends through "
                    + "zero and one and has a limit at infinity, hence is constant by Liouville. "
                    + "In the inverse coordinate, the coefficients of u from the subtracted finite "
                    + "parts are their simple-pole coefficients. Their sum is the derivative at "
                    + "zero of the scalar inverse-coordinate remainder.")),
            T("three-puncture-residue-sum", "residue_sum",
                "Residue balance from the scalar inverse germ",
                Text("Assume G is holomorphic on ℂ ∖ {0, 1} and has finite Laurent expansions "
                    + "with analytic remainders at zero, one and in the scalar germ G(u⁻¹) at zero. "
                    + "For the differential G(z) dz the pullback by z = u⁻¹ multiplies G(u⁻¹) "
                    + "by −u⁻². Its residue at infinity is therefore minus the derivative of the "
                    + "analytic scalar remainder at zero. The three residues sum to zero. "),
                Ref(Prefix + "deriv_inverse_remainder")),
            T("three-puncture-inverse-differential", "inverse_differential_principalPart",
                "Inversion of the differential",
                Text("Assume the scalar germ G(u⁻¹) has a finite Laurent expansion with "
                    + "remainder analytic at u = 0. The inversion Jacobian shifts the scalar principal part by two "
                    + "powers and negates it. The constant term of the scalar remainder then "
                    + "contributes a double pole and the linear term contributes the simple pole.")),
            D("three-puncture-iterate-coordinate", "aChart", "Iterate coordinate at one",
                DescribeRole.Definition,
                Text("For u = z − 1 the iterate residue coordinate is t = −u/(1 + u).")),
            T("three-puncture-iterate-residue", "aChart_residue_invariant",
                "Simple-pole coefficient in the iterate coordinate",
                Text("Assume F has a finite Laurent expansion with remainder analytic at t = 0. "
                    + "Pull back the differential F(t) dt by t = −u/(1 + u). A simple pole "
                    + "becomes u⁻¹ − (1 + u)⁻¹, and each pole of order j ≥ 2 becomes a "
                    + "constant times u^(−j)(1 + u)^(j−2). Its finite expansion has only poles "
                    + "of order at least two. The pulled-back analytic remainder stays analytic, "
                    + "so the simple coefficient is preserved.")),
            T("three-puncture-unique-simple-coefficient", "simpleCoeff_unique",
                "Independence of the Laurent presentation",
                Text("Two finite Laurent presentations of the same punctured germ, with "
                    + "remainders analytic at zero, have the same simple coefficient. "
                    + "Clear both pole bounds and compare the Taylor "
                    + "coefficients of the resulting analytic germs.")),
            T("three-puncture-balance-inverse-expansion", "residue_sum_of_pullback_expansion",
                "Using any Laurent presentation of the inverse differential",
                Text("Assume G is holomorphic on ℂ ∖ {0, 1} and has finite Laurent expansions "
                    + "at zero and one with remainders analytic at their respective centers. "
                    + "Assume both G(u⁻¹) and −u⁻²G(u⁻¹) have finite Laurent expansions with "
                    + "remainders analytic at u = 0. By uniqueness of the simple coefficient, "
                    + "the simple coefficients at zero and one and that of −u⁻²G(u⁻¹) sum to zero. "),
                Ref(Prefix + "simpleCoeff_unique")),
            T("three-puncture-differential-expansions", "residue_sum_of_differential_expansions",
                "Residue balance from three differential expansions",
                Text("Assume G is holomorphic on ℂ ∖ {0, 1}. Supply finite Laurent expansions "
                    + "for G at zero and one and for −u⁻²G(u⁻¹) at u = 0, each with a remainder "
                    + "analytic at its center. Multiplication by −u² shifts the inverse differential "
                    + "coefficients by two exponents and absorbs its simple and double poles into "
                    + "the analytic scalar remainder. The three differential simple coefficients "
                    + "sum to zero. "),
                Ref(Prefix + "residue_sum_of_pullback_expansion")))));

    private static DocumentBlock T(string id, string declaration, string title, params Inline[] content) =>
        D(id, declaration, title, DescribeRole.Theorem, content);

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
