using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class MeasurementMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Observer/MeasurementMarginal",
            "Any surviving indexed address record keeps the system marginal off-diagonal-free."),
        H("Copied-Record Measurement Marginals"),
        Blocks(
            Paragraph(Text(
                "Library-search note: local mathlib and D5 searches for partial trace, environment "
                + "marginal, unread state, pinching, Lueders, and projective measurement found no theorem "
                + "for this concrete copied-record marginal or its partially erased indexed-copy form. "
                + "The proofs reuse the EnvironmentRecords definitions and the finite sum/product lemmas "
                + "from mathlib.")),
            Paragraph(Text(
                "Interface deviation: Conditioning is absent from this worktree's origin/dev base. This "
                + "module does not duplicate IsRecordMeasurement or unreadState; it states the concrete "
                + "address-block sum directly. The generic controlled-record trace identity is owned by "
                + "EnvironmentRecords. Once Conditioning lands, a downstream bridge may identify the block "
                + "sum with its canonical unread state.")),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("copied-record-marginal-is-the-address-block-sum"),
                H("Copied-record marginal is the address-block sum"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_eq_address_blocks"),
                CopiedMarginalFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The copiedAddressRecord is the delta record that writes system address i into the "
                    + "matching environment address. Its Gram overlaps are one on equal addresses and zero "
                    + "otherwise. The retained system marginal is therefore the sum of P_a rho P_a over "
                    + "the two address projectors. The formula is stated directly so Conditioning remains "
                    + "the sole owner of the unread-state definition.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("any-surviving-address-copy-blocks-renewed-coherence"),
                H("Any surviving address copy blocks renewed coherence"),
                LeanTheorem(
                    "D5/S3/Observer/MeasurementMarginal.surviving_copied_record_offDiagonal_eq_zero"),
                SurvivingCopyFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Let R be a finite index family of independent environment records and let A be the "
                    + "set of erased indices. The retained marginal multiplies rho_ij by the Gram overlap "
                    + "from every index outside A. If any surviving index carries copiedAddressRecord, its "
                    + "overlap is zero for i distinct from j, so the whole product and the marginal entry "
                    + "are zero. Full erasure is deliberately outside the theorem's premise.")))
            ))));

    private static Formula CopiedMarginalFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Esc,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Open, Joint("copy"), Close, Eq,
        Sum, Underscore, Grp(F.Id("a"), InMacro, Operatorname, Grp(F.Id("Fin")), Open, D(2), Close),
        F.Id("P"), Underscore, Grp(F.Id("a")), Rho,
        F.Id("P"), Underscore, Grp(F.Id("a")), Dot));

    private static Formula SurvivingCopyFormula() => Disp(Seq(
        Forall, Sp, Kappa, Comma, Esc,
        Forall, Sp, F.Id("R"), Colon, Sp, Kappa, To, Sp,
        Operatorname, Grp(F.Id("EnvironmentRecord")), Comma, Esc,
        Forall, Sp, F.Id("A"), Subset, Underscore, Grp(Operatorname, Grp(F.Id("fin"))),
        Kappa, Comma, Rho, Comma,
        F.Id("i"), Comma, F.Id("j"), Comma, Esc,
        Open, Exists, Sp, F.Id("s"), InMacro, Sp, Kappa, Setminus, F.Id("A"), Comma, Esc,
        F.Id("R"), Underscore, Grp(F.Id("s")), Eq, F.Id("copy"), Close,
        Sp, Land, Sp, F.Id("i"), Neq, Sp, F.Id("j"), Sp, Rightarrow, Sp,
        RetainedMarginal(), Underscore, Grp(F.Id("ij")), Eq, D(0), Dot));

    private static Formula RetainedMarginal() => Seq(
        F.Id("M"), Underscore, Grp(F.Id("R"), Comma, F.Id("A")), Open, Rho, Close);

    private static Formula Joint(string record) => Seq(
        F.Id("J"), Underscore, Grp(F.Id(record)), Open, Rho, Close);
}
