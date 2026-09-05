using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class ComplexPowerSolenoidDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible nonzero complex power threads split into one real logarithmic charge and "
            + "one universal-solenoid phase thread.",
        H("Complex Power-Solenoid Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-norm-charge-is-conserved-across-levels"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/ComplexPowerSolenoidDecomposition."
                        + "logarithmic_charge_conservation"),
                H("The logarithmic norm charge is conserved"),
                StatementSource.FromAuthor(ChargeConservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A complex power thread has nonzero coordinates z_m at every positive "
                            + "level and satisfies z_(mn)^n = z_m. Taking norms at the bonding "
                            + "law and applying Real.log_pow proves that m log(norm(z_m)) is "
                            + "independent of m. The conserved value Q(z) is its level-one "
                            + "value log(norm(z_1)). Explicit nonzero coordinates exclude the "
                            + "totalized Real.log zero branch.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Complex.norm_pow and Real.log_pow. Repository, "
                            + "digest, generalized, and in-flight searches found no existing "
                            + "compatible complex power tower or conserved logarithmic charge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-power-threads-split-into-charge-and-phase"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/ComplexPowerSolenoidDecomposition."
                        + "complexPowerThreadEquiv"),
                H("Complex power threads split into charge and phase"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Normalize each coordinate by its positive norm. The resulting unit "
                            + "complex numbers preserve every bonding power and therefore define "
                            + "a point of the repository's UniversalSolenoid through Mathlib's "
                            + "AddCircle.homeomorphCircle. Conversely, a charge q and a solenoid "
                            + "phase theta assemble level m as exp(q/m) times the circle value "
                            + "of theta_m.")),
                    Paragraph(Text(
                        "Real.exp_nat_mul proves compatibility of the radial factors, while "
                            + "AddCircle.toCircle_nsmul proves compatibility of the phases. "
                            + "The formal construction proves both inverse laws, so this is a "
                            + "constructive equivalence rather than a cardinality assertion.")),
                    Paragraph(Text(
                        "The source statement is corrected to this supported algebraic core. "
                            + "It called the first factor R_Q without defining a different real "
                            + "structure and additionally asserted RH, maximal-compact, zero-thread, "
                            + "Gamma-factor, and trivial-zero claims that do not follow from the "
                            + "power-thread data. Those unsupported clauses are not claimed here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("every-real-logarithmic-charge-has-a-thread-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/ComplexPowerSolenoidDecomposition."
                        + "logarithmicCharge_surjective"),
                H("Every real charge has an explicit thread witness"),
                StatementSource.FromAuthor(SurjectiveChargeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each real q, assemble q with the zero universal-solenoid phase. Its "
                        + "level-one logarithmic norm is exactly q, giving the required witness "
                        + "and showing that the Archimedean factor is genuinely unrestricted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-charge-is-exactly-the-unit-norm-locus"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/ComplexPowerSolenoidDecomposition."
                        + "logarithmicCharge_eq_zero_iff"),
                H("Zero charge is exactly the unit-norm locus"),
                StatementSource.FromAuthor(ZeroChargeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Charge conservation and positivity of every coordinate norm show that zero "
                        + "charge forces log(norm(z_m)) = 0 and hence norm(z_m) = 1 at every "
                        + "level. Conversely, the level-one unit norm makes the charge zero. "
                        + "This supplies both directions of the compact-phase characterization."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Dynamics/UniversalSolenoid")),
        ]));

    private static Formula ChargeConservationFormula()
    {
        Formula z = F.Id("z");
        Formula m = F.Id("m");
        Formula zm = Seq(z, Underscore, Grp(m));

        return Disp(Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ComplexPowerThread")),
            Comma, Sp, m, Colon, Sp, Operatorname, Grp(F.Id("PositiveNat")), Comma, Esc,
            m, Sp, Cdot, Sp, Log, Open, Call("norm", zm), Close,
            Sp, Eq, Sp, Call("Q", z), Dot));
    }

    private static Formula DecompositionFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("ComplexPowerThread")), Sp, Equiv, Sp,
        Mathbb, Grp(F.Id("R")), Sp, Times, Sp, Mathcal, Grp(F.Id("S")), Comma, Quad, Sp,
        F.Id("z"), Sp, Mapsto, Sp, Open, Call("Q", F.Id("z")), Comma, Sp,
        Call("phase", F.Id("z")), Close, Dot));

    private static Formula SurjectiveChargeFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Surjective")), Open, F.Id("Q"), Close, Dot));

    private static Formula ZeroChargeFormula()
    {
        Formula z = F.Id("z");
        Formula m = F.Id("m");

        return Disp(Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ComplexPowerThread")),
            Comma, Esc, Call("Q", z), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Forall, Sp, m, Colon, Sp, Operatorname, Grp(F.Id("PositiveNat")), Comma, Esc,
            Call("norm", Seq(z, Underscore, Grp(m))), Sp, Eq, Sp, D(1), Dot));
    }
}
