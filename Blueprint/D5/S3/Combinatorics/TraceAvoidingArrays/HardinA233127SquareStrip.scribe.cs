using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127RowsDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127SquareStripDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233127");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin’s recurrence for normalized six-column complementary-pair square strips.",
        H("The finite certificate and the all-height recurrence"),
        Blocks(
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Single-row certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Exact scanner fibres reduce the transition counts to 3^6 label rows. "
                    + "The single-row certificate supplies the numerical premises of the "
                    + "all-height induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The recurrence at every height"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of "
                    + "D5.S3.Observer.Separation.BooleanRankThreeK4.beta. Exact scanner fibres "
                    + "retain the order restrictions and individual colour multiplicities. "
                    + "The first-row distribution is (16,0,16,16,16,16,16,8,8,16,8). "
                    + "The displayed matrix counts continuations from each valid boundary. "
                    + "A class-constant continuation remains class-constant after one row, "
                    + "hence after every number of rows by semiconjugacy iteration. The "
                    + "unseen sector has eigenvalue 64. The ten completed classes have "
                    + "characteristic polynomial x^3 times "
                    + "(x^7-1920x^6+1191936x^5-335020032x^4+48670703616x^3"
                    + "-3778497478656x^2+147884313935872x-2269391999729664). "
                    + "The full initial row vector is annihilated by (x-64) times that "
                    + "degree-seven cofactor. Its eighth transfer is exactly the indicated "
                    + "linear combination of its first eight distributions, coordinate by "
                    + "coordinate. Pairing this identity with any continuation height proves "
                    + "the recurrence for the literal filtered count at every n+9."))),
                DescribeRole.Theorem))));

}
