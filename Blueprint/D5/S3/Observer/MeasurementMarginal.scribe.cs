using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class MeasurementMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Observer/MeasurementMarginal",
            "Copied address records identify unread measurement marginals and block renewed coherence."),
        H("Copied-Record Measurement Marginals"),
        Blocks(
            Paragraph(Text(
                "Library-search note: local mathlib and D5 searches for partial trace, environment "
                + "marginal, unread state, pinching, and Lueders found no theorem identifying this "
                + "concrete controlled-record marginal with an unread measurement map. The formal "
                + "proof therefore reuses the joint-state, environment-trace, overlap, and record-channel "
                + "definitions from EnvironmentRecords and the finite-sum factorization from mathlib.")),
            Paragraph(Text(
                "Temporary interface deviation: Conditioning is absent from the origin/dev base of this "
                + "worktree. MeasurementMarginal reproduces only its IsRecordMeasurement and unreadState "
                + "interfaces with matching signatures. Once Conditioning lands, these two local declarations "
                + "are to be removed and imported from that module; no compatibility alias is intended.")),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("standard-address-projectors-form-a-record-measurement"),
                H("Standard address projectors form a record measurement"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.addressProjection_isRecordMeasurement"),
                AddressMeasurementFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For each of the two system addresses, P_a is the diagonal matrix with one only at "
                    + "entry (a,a). These two matrices are self-adjoint and idempotent, distinct projectors "
                    + "multiply to zero, and their sum is the identity. This supplies the concrete record "
                    + "measurement used by the marginal bridge.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("controlled-record-environment-trace-is-the-record-channel"),
                H("Controlled-record environment trace is the record channel"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.trace_environment_controlled_record_eq_record_channel"),
                TraceChannelFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every two-component environment record R and every complex qubit matrix rho, "
                    + "tracing the environment of the controlled-record joint matrix multiplies each "
                    + "system entry rho_ij by the Gram overlap of records i and j. This is exactly the "
                    + "recordChannel definition. Unlike the earlier phase-damping theorem, this identity "
                    + "does not require a constant off-diagonal Gram overlap.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("copied-record-marginal-is-the-unread-address-state"),
                H("Copied-record marginal is the unread address state"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_eq_unread"),
                CopiedMarginalFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The copiedAddressRecord is the delta record that writes system address i into the "
                    + "matching environment address. Its Gram overlaps are one on equal addresses and zero "
                    + "otherwise. The retained system marginal is therefore the sum of P_a rho P_a over "
                    + "the two address projectors, exactly the unread measurement state.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("one-surviving-address-copy-blocks-renewed-coherence"),
                H("One surviving address copy blocks renewed coherence"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_offDiagonal_eq_zero"),
                OffDiagonalFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For distinct system addresses i and j, the marginal left by one orthogonal copied "
                    + "record has entry (i,j) equal to zero for every input rho. Thus retaining one such "
                    + "copy gives a directly decidable no-recoherence statement. The theorem does not "
                    + "introduce a copy index, subset-erasure operation, recovery operation, or dynamics "
                    + "beyond this surviving-copy marginal.")))
            ))));

    private static Formula AddressMeasurementFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("RecordMeasurement")), Open,
        F.Id("P"), Underscore, Grp(F.Id("address")), Close, Dot));

    private static Formula TraceChannelFormula() => Disp(Seq(
        Forall, Sp, F.Id("R"), Comma, Rho, Comma, Esc,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Open, Joint("R"), Close, Eq,
        F.Id("C"), Underscore, Grp(F.Id("R")), Open, Rho, Close, Dot));

    private static Formula CopiedMarginalFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Esc,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Open, Joint("copy"), Close, Eq,
        F.Id("U"), Underscore, Grp(F.Id("P"), Underscore, Grp(F.Id("address"))),
        Open, Rho, Close, Dot));

    private static Formula OffDiagonalFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, F.Id("i"), Comma, F.Id("j"), Comma, Esc,
        F.Id("i"), Neq, Sp, F.Id("j"), Sp, Rightarrow, Sp,
        Open, Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Open, Joint("copy"), Close, Close,
        Underscore, Grp(F.Id("ij")), Eq, D(0), Dot));

    private static Formula Joint(string record) => Seq(
        F.Id("J"), Underscore, Grp(F.Id(record)), Open, Rho, Close);
}
