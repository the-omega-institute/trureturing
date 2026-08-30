using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class PerfectRecordMirrorReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A perfect unread record erases every mirror observable with no record-diagonal block.",
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
                        "For a finite complete family of pairwise orthogonal self-adjoint "
                            + "complex matrix projections, the unread map is the sum of the "
                            + "diagonal compressions P_k rho P_k.")),
                    Paragraph(Text(
                        "If an observable has zero diagonal block P_k J P_k for every record "
                            + "value, cyclicity of the matrix trace makes its pairing with the "
                            + "unread state vanish. The same statement also records that the "
                            + "unread map preserves the trace of rho.")),
                    Paragraph(Text(
                        "The companion incompatibility corollary states that a nonzero unread "
                            + "readout must retain a nonzero record-diagonal block; qualitative "
                            + "observer-ontology alternatives in the source are not additional "
                            + "mathematical clauses."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula labels = F.Id("K");
        Formula projectionFamily = F.Id("P");
        Formula rho = F.Id("rho");
        Formula observable = F.Id("J");
        Formula index = F.Id("k");
        Formula matrix = MatrixType(n);
        Formula channel = Seq(F.Id("E"), Underscore, Grp(projectionFamily));
        Formula unread = Apply(channel, rho);
        Formula diagonalCondition = Seq(
            Open, Forall, Sp, index, Colon, Sp, labels, Comma, Sp,
            Subscript(projectionFamily, index), Sp, observable, Sp,
            Subscript(projectionFamily, index), Sp, Eq, Sp, D(0), Close);
        Formula conclusion = Seq(
            Call("Tr", Seq(unread, observable)), Sp, Eq, Sp, D(0), Sp,
            Land, Sp,
            Call("Tr", unread), Sp, Eq, Sp, Call("Tr", rho));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Comma, Sp, labels, Comma, Sp,
            Call("Fintype", n), Comma, Sp, Call("DecidableEq", n), Comma, Sp,
            Call("Fintype", labels),
            RowBreak, Grp(),
            projectionFamily, Colon, Sp, labels, Sp, To, Sp, matrix, Comma,
            RowBreak, Grp(),
            Call("IsRecordMeasurement", projectionFamily), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, rho, Colon, Sp, matrix, Comma, Sp,
            Forall, Sp, observable, Colon, Sp, matrix, Comma, Sp,
            diagonalCondition, Sp, Rightarrow, Sp,
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MatrixType(Formula n) => Seq(
        F.Id("M"), Underscore, Grp(n), Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
