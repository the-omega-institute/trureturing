using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class MeasurementMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A copied address record makes the traced system marginal off-diagonal-free.",
        H("Copied-Record Measurement Marginals"),
        Blocks(
            Paragraph(Text(
                "Library-search note: local mathlib and D5 searches for partial trace, environment "
                + "marginal, unread state, pinching, Lueders, and projective measurement found no theorem "
                + "identifying this concrete copied-record marginal with an unread measurement map. The "
                + "proofs reuse the EnvironmentRecords definitions and finite-sum lemmas from mathlib.")),
            Paragraph(Text(
                "Interface deviation: Conditioning is absent from this worktree's origin/dev base. This "
                + "module does not duplicate IsRecordMeasurement or unreadState; it states the concrete "
                + "address-block sum directly. The generic controlled-record trace identity is owned by "
                + "EnvironmentRecords. Once Conditioning lands, a downstream bridge may identify the block "
                + "sum with its canonical unread state.")),
            Paragraph(Text(
                "Unresolved: a multiple-environment statement requires a joint state over all copy "
                + "factors, a subsystem partial trace, and an explicit erasure operation. Those generic "
                + "quantum constructions are deferred to an environment-infrastructure round rather than "
                + "postulated in this Observer module.")),
            Describe.Lean(
                DescribeId.Create("copied-record-marginal-is-the-address-block-sum"),
                DeclarationHandle.Create("D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_eq_address_blocks"),
                H("Copied-record marginal is the address-block sum"),
                StatementSource.FromAuthor(CopiedMarginalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The copiedAddressRecord is the delta record that writes system address i into the "
                                    + "matching environment address. Its Gram overlaps are one on equal addresses and zero "
                                    + "otherwise. The retained system marginal is therefore the sum of P_a rho P_a over "
                                    + "the two address projectors. The formula is stated directly so Conditioning remains "
                                    + "the sole owner of the unread-state definition."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("one-copied-address-record-has-zero-off-diagonal-marginal"),
                DeclarationHandle.Create("D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_offDiagonal_eq_zero"),
                H("One copied address record has zero off-diagonal marginal"),
                StatementSource.FromAuthor(CopiedOffDiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The theorem starts with the explicit controlledRecordJointState for the delta record "
                                    + "and applies traceEnvironment. The derived address-block identity leaves only diagonal "
                                    + "system entries, so every entry with i distinct from j is zero."))),
                DescribeRole.Theorem
            ))));

    private static Formula CopiedMarginalFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Esc,
        Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Open, Joint(F.Id("copy")), Close, Eq,
        Sum, Underscore, Grp(F.Id("a"), InMacro, Operatorname, Grp(F.Id("Fin")), Open, D(2), Close),
        F.Id("P"), Underscore, Grp(F.Id("a")), Sp, Rho, Sp,
        F.Id("P"), Underscore, Grp(F.Id("a")), Dot));

    private static Formula CopiedOffDiagonalFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, F.Id("i"), Comma, F.Id("j"), Comma, Esc,
        F.Id("i"), Neq, Sp, F.Id("j"), Sp, Rightarrow, Sp,
        Open, Operatorname, Grp(F.Id("tr")), Underscore, Grp(F.Id("E")),
        Joint(F.Id("copy")), Close, Underscore, Grp(F.Id("ij")), Eq, D(0), Dot));

    private static Formula Joint(Formula record) => Seq(
        F.Id("J"), Underscore, Grp(record), Open, Rho, Close);
}
