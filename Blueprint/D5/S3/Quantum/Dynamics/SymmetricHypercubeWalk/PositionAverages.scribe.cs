using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class PositionAveragesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pointwise position averages give probability laws at every finite dimension.",
        H("Position masses and their Cesàro limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tendsto-continuousaverage"),
                DeclarationHandle.Create(Prefix + "tendsto_continuousAverage"),
                H("Real-horizon continuous-time average"),
                StatementSource.FromAuthor(Disp(Seq(Frac, Grp(D(1)), Grp(F.Id("T")), Sp, Int, Underscore, Grp(D(0)), Caret, Grp(F.Id("T")), Sp, F.Id("p"), Underscore, Grp(F.Id("C")), Open, F.Id("t"), Comma, F.Id("x"), Close, Sp, F.Id("dt"), Sp, To, Sp, Overline, Grp(F.Id("p")), Underscore, Grp(F.Id("C")), Open, F.Id("x"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The CT position mass is the squared complex norm of the origin amplitude. T tends to infinity through real horizons. The limiting mass is the Walsh expansion with the pairwise equality indicator. Its masses are nonnegative and sum to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tendsto-discreteaverage"),
                DeclarationHandle.Create(Prefix + "tendsto_discreteAverage"),
                H("Integer-horizon discrete-time average"),
                StatementSource.FromAuthor(Disp(Seq(Frac, Grp(D(1)), Grp(F.Id("T")), Sp, Sum, Underscore, Grp(F.Id("n"), Eq, D(0)), Caret, Grp(F.Id("T"), Minus, D(1)), Sp, F.Id("p"), Underscore, Grp(F.Id("D")), Open, F.Id("n"), Comma, F.Id("x"), Close, Sp, To, Sp, Overline, Grp(F.Id("p")), Underscore, Grp(F.Id("D")), Open, F.Id("x"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The DT mass sums the squared complex norms over the coin, as checked by discreteMass_eq_complex. T tends to infinity through natural horizons. The limiting masses also form a probability law. Walsh orthogonality reduces each character observable to ordered pairs (a,a XOR c)."))),
                DescribeRole.Theorem))));
}
