using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class SubshiftTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Word subshifts are closed orbit closures, and the golden subshift is perfect with "
            + "cardinality continuum.",
        H("Topology and Cardinality of Word Subshifts"),
        Blocks(
            Paragraph(Text(
                "For a one-sided word x, let X_x contain the infinite words whose prefixes all "
                + "occur as factors of x. Product cylinders expose both the topology of X_x and "
                + "the approximation supplied by the forward shift orbit.")),
            Describe.Lean(
                DescribeId.Create("word-subshift-closed"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftTopology.isClosed_wordSubshift"),
                H("Every word subshift is closed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Closed")), Open, F.Id("X"), Underscore,
                    F.Id("x"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each prefix length, the admissible words form a finite union of closed "
                    + "FullShift cylinders. Intersecting these closed level conditions over all "
                    + "natural lengths gives exactly X_x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("word-subshift-orbit-closure"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftTopology."
                        + "closure_shift_orbit_eq_wordSubshift"),
                H("The forward orbit closure equals the word subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("cl")), Open, Operatorname, Grp(F.Id("Orb")),
                    Caret, Plus, Open, F.Id("x"), Close, Close, Sp, Eq, Sp, F.Id("X"),
                    Underscore, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Closedness and shift invariance place the orbit closure inside X_x. For the "
                    + "reverse inclusion, every prefix admitted by X_x occurs at some starting "
                    + "position of x, so the corresponding shift enters the required PiNat "
                    + "cylinder neighborhood."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-word-subshift-perfect"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftTopology.golden_wordSubshift_perfect"),
                H("The golden word subshift is perfect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Perfect")), Open, F.Id("X"), Underscore,
                    F.Id("g"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Golden recurrence realizes every admitted prefix at arbitrarily late "
                        + "positions, producing orbit points in every cylinder neighborhood.")),
                    Paragraph(Text(
                        "The exact factor count n+1 rules out equal golden suffixes: equality of "
                        + "two suffixes would make all length-j factors representable by fewer "
                        + "than j+1 starts. Two recurrent occurrences therefore provide a point "
                        + "different from the prescribed center in every neighborhood."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-word-subshift-continuum-cardinality"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftTopology."
                        + "golden_wordSubshift_cardinal_eq_continuum"),
                H("The golden word subshift has cardinality continuum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Underscore,
                    F.Id("g"), Close, Sp, Eq, Sp, F.Id("c")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's perfect-set injection embeds Cantor space into the nonempty "
                        + "golden subshift after equipping Bool sequences with the compatible "
                        + "complete PiNat metric. This gives the continuum lower bound.")),
                    Paragraph(Text(
                        "The ambient function space from natural numbers to Bool has cardinality "
                        + "continuum, so subtype monotonicity supplies the matching upper bound. "
                        + "Here c denotes the continuum cardinal."))),
                DescribeRole.Theorem))));
}
