using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class BasisMeasurementProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Basis measurement is the orthogonal projection onto diagonal Hermitian operators, including on the trace-zero carrier.",
        H("Basis-Measurement Projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("basis-measurement-equals-its-projector-coordinate-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_eq_projector_sum"),
                H("Basis measurement is the sum of its trace coordinates"),
                StatementSource.FromAuthor(ProjectorSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rank-one context B consists of d Hermitian idempotents P_j with trace one, sum equal to the identity, and P_j X P_j = trace(P_j X) times P_j for every matrix X. HermitianSpace(d) is the real space of matrices equal to their conjugate transpose. The vector basisProjector(B,j) is P_j in this space, and basisMeasurement(B,A) has underlying matrix the sum of P_j A P_j. For Hermitian A each trace coordinate is real, so the compression sum is exactly the displayed real linear combination. The conclusion includes dimension zero and requires no NeZero instance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basis-projector-has-the-context-projector-as-its-matrix"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisProjector_val"),
                H("A basis projector retains its underlying matrix"),
                StatementSource.FromAuthor(BasisProjectorValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A basis projector is the context projector equipped with its "
                            + "Hermitian certificate. Forgetting that certificate returns the "
                            + "original projector matrix exactly, so the real Hermitian-space "
                            + "carrier does not alter the operator."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-measurement-agrees-with-unread-state-on-values"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisMeasurement_val"),
                H("Basis measurement is unread measurement on matrices"),
                StatementSource.FromAuthor(BasisMeasurementValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real-linear basis-measurement operator is the unread measurement "
                            + "channel restricted to Hermitian matrices. On underlying matrices, "
                            + "its value is precisely the sum of the basis compressions, with no "
                            + "additional normalization or projection step."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-measurement-preserves-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection."
                        + "basis_measurement_trace"),
                H("Complete basis measurement preserves trace"),
                StatementSource.FromAuthor(BasisMeasurementTraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a complete projective record measurement, the diagonal-block sum "
                            + "has the same trace as the input Hermitian matrix. Consequently the "
                            + "basis-measurement restriction preserves the affine trace slices, "
                            + "in particular the trace-zero subspace."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-measurement-range-is-the-diagonal-subspace"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection."
                        + "basis_measurement_range"),
                H("The range is exactly the diagonal Hermitian subspace"),
                StatementSource.FromAuthor(BasisMeasurementRangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every measured Hermitian operator is a real linear combination of the "
                            + "context's rank-one projectors, so the image lies in their span. "
                            + "Conversely, each basis projector is fixed by the measurement, "
                            + "which makes every generator, and hence the entire diagonal span, "
                            + "belong to the image."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-measurement-is-the-diagonal-orthogonal-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection."
                        + "basis_measurement_is_orthogonal_projection"),
                H("Basis measurement is the diagonal orthogonal projection"),
                StatementSource.FromAuthor(BasisMeasurementProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A complete rank-one basis measurement is idempotent and symmetric for "
                            + "the real Hilbert--Schmidt inner product. Together with the exact "
                            + "range calculation, this identifies the measurement with the "
                            + "orthogonal projection onto the diagonal Hermitian subspace.")),
                    Paragraph(Text(
                        "For every Hermitian input, the discarded off-diagonal component is "
                            + "orthogonal to every diagonal Hermitian operator. Thus the theorem "
                            + "records both the projection operator and its defining residual "
                            + "orthogonality, rather than only idempotence or range containment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "trace-zero-basis-measurement-is-the-trace-zero-diagonal-projection"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/BasisMeasurementProjection."
                        + "trace_zero_basis_measurement_is_orthogonal_projection"),
                H("The trace-zero restriction projects onto trace-zero diagonals"),
                StatementSource.FromAuthor(TraceZeroBasisMeasurementProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Trace preservation makes the trace-zero Hermitian carrier invariant "
                            + "under basis measurement. The restricted real-linear operator "
                            + "remains idempotent and symmetric, so it is an orthogonal projection.")),
                    Paragraph(Text(
                        "Its range is exactly the diagonal operators whose trace is zero. The "
                            + "reverse inclusion uses trace preservation to choose a trace-zero "
                            + "preimage, ruling out the weaker conclusion of mere containment in "
                            + "the diagonal trace-zero subspace."))),
                DescribeRole.Lemma))));

    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula SumAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);

    private static Formula ProjectorSumFormula()
    {
        var d = F.Id("d"); var b = F.Id("B"); var a = F.Id("A"); var j = F.Id("j");
        var matrix = Seq(Parenthesized(a), Dot, D(1));
        var coordinate = Call("re", Call("trace", Multiply(Call("projector", b, j), matrix)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(j, Colon, Sp, Call("Fin", d))), Sp,
            Call("smul", coordinate, Call("basisProjector", b, j)));
        return Disp(SumAll("d", Seq(Mathbb, Grp(F.Id("N"))),
            SumAll("B", Call("RankOneContext", d), SumAll("A", Call("HermitianSpace", d),
                Equal(Call("basisMeasurement", b, a), sum)))));
    }

    private static Formula BasisProjectorValueFormula()
    {
        Formula basis = F.Id("B");
        Formula index = F.Id("j");
        return Disp(Seq(
            Forall, Sp, basis, Comma, Sp, index, Comma, Sp,
            Call("val", Call("basisProjector", basis, index)), Sp, Eq, Sp,
            Call("projector", basis, index), Dot));
    }

    private static Formula BasisMeasurementValueFormula()
    {
        Formula basis = F.Id("B");
        Formula matrix = F.Id("A");
        return Disp(Seq(
            Forall, Sp, basis, Comma, Sp, matrix, Comma, Sp,
            Call("val", Call("basisMeasurement", basis, matrix)), Sp, Eq, Sp,
            Call("unreadState", Call("projector", basis), Call("val", matrix)), Dot));
    }

    private static Formula BasisMeasurementTraceFormula()
    {
        Formula basis = F.Id("B");
        Formula matrix = F.Id("A");
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));
        return Disp(Seq(
            Forall, Sp, basis, Comma, Sp, matrix, Comma, Sp,
            recordMeasurement, Sp, Rightarrow, Sp,
            Call("Tr", Call("val", Call("basisMeasurement", basis, matrix))), Sp, Eq, Sp,
            Call("Tr", Call("val", matrix)), Dot));
    }

    private static Formula BasisMeasurementRangeFormula()
    {
        Formula basis = F.Id("B");
        Formula measurement = Call("basisMeasurement", basis);
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));
        return Disp(Seq(
            Forall, Sp, basis, Comma, Sp,
            recordMeasurement, Sp, Rightarrow, Sp,
            Call("range", measurement), Sp, Eq, Sp,
            Call("diagonalSubspace", basis), Dot));
    }

    private static Formula BasisMeasurementProjectionFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula matrix = F.Id("A");
        Formula diagonal = F.Id("D");
        Formula measurement = Call("basisMeasurement", basis);
        Formula measuredMatrix = Call("basisMeasurement", basis, matrix);
        Formula diagonalSpace = Call("diagonalSubspace", basis);
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            recordMeasurement, Sp, Rightarrow, RowBreak, Grp(),
            Call("IsSymmetricProjection", measurement), Sp, Land, RowBreak, Grp(),
            Call("range", measurement), Sp, Eq, Sp, diagonalSpace, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, matrix, Comma, Sp,
            diagonal, Colon, Sp, Call("HermitianSpace", dimension), Comma, Sp,
            diagonal, Sp, InMacro, Sp, diagonalSpace, Sp, Rightarrow, Sp,
            Call("innerR", Seq(matrix, Sp, Minus, Sp, measuredMatrix), diagonal),
            Sp, Eq, Sp, D(0), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TraceZeroBasisMeasurementProjectionFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula measurement = Call("traceZeroBasisMeasurement", basis);
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            recordMeasurement, Sp, Rightarrow, RowBreak, Grp(),
            Call("IsSymmetricProjection", measurement), Sp, Land, RowBreak, Grp(),
            Call("range", measurement), Sp, Eq, Sp,
            Call("diagonalTraceZeroSubspace", basis), Dot));
    }
}
