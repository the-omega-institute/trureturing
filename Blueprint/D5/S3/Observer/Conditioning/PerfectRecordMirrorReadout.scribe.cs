using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class PerfectRecordMirrorReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discarding a perfect two-address record erases the fixed mirror-swap expectation.",
        H("Perfect Record Mirror Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("perfect-record-mirror-readout-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout."
                        + "perfect_record_mirror_readout_zero"),
                H("Perfect recording forces zero mirror expectation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state rho is an arbitrary complex matrix on the canonical two-address "
                            + "carrier. The standard address projectors define the unread map, and "
                            + "qubitX is the fixed observable that exchanges the two addresses.")),
                    Paragraph(Text(
                        "Each address compression has zero pairing with the off-diagonal swap. "
                            + "Cyclicity and linearity of the matrix trace therefore make the "
                            + "pairing with unreadState addressProjection rho vanish.")),
                    Paragraph(Text(
                        "This declaration owns only the displayed zero-expectation clause. The "
                            + "ledger atom remains guarded because its later classical-label, "
                            + "five-way-alternative, and observer-ontology clauses have no current "
                            + "public carrier."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rho = F.Id("rho");
        Formula twoAddresses = Call("Fin", D(2));
        Formula matrix = MatrixType(twoAddresses);
        Formula unread = Call("unreadState", F.Id("addressProjection"), rho);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Colon, Sp, matrix, Comma, Sp,
            Call("Tr", Seq(unread, Sp, Cdot, Sp, F.Id("qubitX"))),
            Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);

}
