using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ZetaThermalStatePinchingFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Basis pinching fixes exactly the diagonal Hermitian operators and therefore fixes finite zeta thermal states in their defining basis.",
        H("Finite Zeta Thermal States Are Fixed by Basis Pinching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("basis-measurement-fixed-points-are-exactly-diagonal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed."
                        + "basis_measurement_eq_self_iff"),
                H("The fixed points of basis measurement are exactly diagonal"),
                StatementSource.FromAuthor(BasisMeasurementFixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a complete rank-one record measurement, a Hermitian operator is "
                            + "unchanged by basis pinching exactly when it lies in the span of "
                            + "the measured basis projectors. Thus the diagonal subspace is the "
                            + "entire fixed-point space, not merely a collection of fixed points."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-zeta-thermal-state-is-diagonal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed."
                        + "zeta_thermal_state_mem_diagonal"),
                H("A finite zeta thermal state is diagonal"),
                StatementSource.FromAuthor(ZetaThermalStateDiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every summand of the finite zeta thermal state is a scalar multiple of "
                            + "one of the defining context's basis projectors. Since their span is "
                            + "a real subspace, the complete finite weighted sum belongs to the "
                            + "diagonal subspace; the common partition factor does not affect "
                            + "this membership."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "finite-zeta-thermal-state-is-fixed-by-basis-pinching"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed."
                        + "zeta_thermal_state_pinching_fixed"),
                H("Basis pinching fixes the finite zeta thermal state"),
                StatementSource.FromAuthor(ZetaThermalStateFixedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite zeta-weighted combination has no component outside the "
                            + "diagonal subspace of its defining context. For a complete record "
                            + "measurement, basis pinching is therefore the identity on this "
                            + "operator, so the thermal combination is left unchanged."))),
                DescribeRole.Theorem))));

    private static Formula BasisMeasurementFixedPointFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula matrix = F.Id("A");
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            matrix, Colon, Sp, Call("HermitianSpace", dimension), Comma, Sp,
            recordMeasurement, Sp, Rightarrow, Sp,
            Open, Call("basisMeasurement", basis, matrix), Sp, Eq, Sp, matrix, Sp,
            Iff, Sp, matrix, Sp, InMacro, Sp, Call("diagonalSubspace", basis), Close, Dot));
    }

    private static Formula ZetaThermalStateDiagonalFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula exponent = F.Id("s");
        Formula support = F.Id("S");

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            exponent, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            support, Colon, Sp, Call("Finset", Call("Fin", dimension)), Comma, Sp,
            Call("zetaThermalState", basis, exponent, support), Sp, InMacro, Sp,
            Call("diagonalSubspace", basis), Dot));
    }

    private static Formula ZetaThermalStateFixedFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula exponent = F.Id("s");
        Formula support = F.Id("S");
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));
        Formula state = Call("zetaThermalState", basis, exponent, support);

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            exponent, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            support, Colon, Sp, Call("Finset", Call("Fin", dimension)), Comma, Sp,
            recordMeasurement, Sp, Rightarrow, Sp,
            Call("basisMeasurement", basis, state), Sp, Eq, Sp, state, Dot));
    }
}
