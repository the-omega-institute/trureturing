using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class EnvironmentRecordsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tracing controlled qubit records gives phase damping under the stated Gram condition, and unit overlaps characterize the record-channel fixed points.",
        H("Environment Records and Selected Fixed Entries"),
        Blocks(
            Paragraph(Text(
                "Let r be a function from Fin(2) to Fin(2) to the complex numbers, "
                + "and let rho be an arbitrary complex two-by-two matrix. The "
                + "record overlap G is the sum of r(i,a) times the complex conjugate "
                + "of r(j,a), over the two environment indices a. The controlled "
                + "joint matrix has entry r(i,a) times the conjugate of r(j,b) "
                + "times rho(i,j) at indices (i,a),(j,b). The environment trace "
                + "sums the entries at (i,a),(j,a).")),
            Describe.Lean(
                DescribeId.Create("controlled-record-trace-is-phase-damping"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/EnvironmentRecords.trace_environment_controlled_record_eq_phase_damping"),
                H("A prescribed record Gram matrix yields phase damping"),
                StatementSource.FromAuthor(TraceFormula()),
                AssessedProvenance.FromRepo(Zurek),
                Blocks(
                    Paragraph(Text(
                        "Let c be a DampingCoefficient, so its real value lies in "
                        + "[0,1]. Suppose, for every i and j in Fin(2), that G(i,j) "
                        + "equals one when i = j and the complex cast of c otherwise. "
                        + "Then tracing the environment out of controlledRecordJointState(r,rho) "
                        + "equals phaseDamping(c,rho). The Gram premise includes unit "
                        + "norm for each record. No positivity, Hermiticity, or "
                        + "trace-one condition is imposed on rho.")),
                    Paragraph(Text(
                        "Entrywise, the finite environment sum factors as "
                        + "G(i,j) times rho(i,j). Substitution of the Gram premise "
                        + "preserves diagonal entries and multiplies every "
                        + "off-diagonal entry by c. Zurek's review supplies the "
                        + "environment-overlap interpretation; this identity "
                        + "is derived from the explicitly defined finite record "
                        + "interaction and assumes the stated overlaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-record-channel-selected-entries"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/EnvironmentRecords.record_channel_fixed_iff_selected_blocks"),
                H("Unit record overlaps select the fixed entries"),
                StatementSource.FromAuthor(FixedFormula()),
                AssessedProvenance.FromRepo(Zurek),
                Blocks(
                    Paragraph(Text(
                        "For every record r and every qubit matrix rho, "
                        + "recordChannel(r,rho) = rho if and only if, for all i "
                        + "and j, G(i,j) different from one implies rho(i,j) = 0. "
                        + "Here recordChannel acts entrywise by multiplication "
                        + "by G. This theorem does not assume the preceding Gram "
                        + "condition or normalized records; the condition also "
                        + "applies to diagonal entries when G(i,i) is not one.")),
                    Paragraph(Text(
                        "The fixed-point equation at an entry is "
                        + "(G(i,j) - 1) times rho(i,j) = 0. Since the complex "
                        + "numbers have no zero divisors, an overlap different from one "
                        + "forces that entry to vanish. Conversely, the "
                        + "vanishing condition makes multiplication by G fix "
                        + "every entry. An interpretation as blocks of identical "
                        + "normalized records requires the corresponding "
                        + "normalization assumptions separately."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula RecordQuantifiers() => Seq(
        Forall, Sp, F.Id("r"), Colon, Call("Fin", D(2)), To,
        Call("Fin", D(2)), To, Mathbb, Grp(F.Id("C")), Comma, Esc,
        Forall, Sp, Rho, Sp, InMacro, Sp, Call("Matrix", Call("Fin", D(2)),
            Call("Fin", D(2)), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc);

    private static Formula EntryQuantifiers() => Seq(
        Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Sp, InMacro, Sp,
        Call("Fin", D(2)), Comma, Esc);

    private static Formula Overlap() =>
        Call("recordOverlap", F.Id("r"), F.Id("i"), F.Id("j"));

    private static Formula TraceFormula() => Disp(Seq(
        RecordQuantifiers(),
        Forall, Sp, F.Id("c"), Sp, InMacro, Sp,
        OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Esc,
        Parenthesized(Seq(EntryQuantifiers(), Overlap(), Sp, Eq, Sp,
            Call("if", Equal(F.Id("i"), F.Id("j")), D(1), F.Id("c")))),
        Sp, Rightarrow, Sp,
        Equal(Call("traceEnvironment", Call("controlledRecordJointState", F.Id("r"), Rho)),
            Call("phaseDamping", F.Id("c"), Rho))));

    private static Formula FixedFormula() => Disp(Seq(
        RecordQuantifiers(),
        Equal(Call("recordChannel", F.Id("r"), Rho), Rho),
        Sp, Iff, Sp,
        Parenthesized(Seq(EntryQuantifiers(), NotEqual(Overlap(), D(1)),
            Sp, Rightarrow, Sp,
            Equal(Seq(Rho, Underscore, Grp(F.Id("i"), F.Id("j"))), D(0))))));
}
