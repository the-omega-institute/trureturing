using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parallel classes of affine lines.",
        H("Parallel classes of affine lines"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-line-direction"),
            DeclarationHandle.Create(Module + ".unique_line"),
            H("A pair of points determines one direction"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("x"), Sp, Neq, Sp, F.Id("y"), Sp, Rightarrow, Sp,
                Exists, Bang, Sp, F.Id("u"), Comma, Sp,
                Call("line", F.Id("u"), F.Id("x")), Sp, Eq, Sp,
                Call("line", F.Id("u"), F.Id("y"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(
                "For two distinct points in the space of k+1 coordinates over a field, normalize their difference at its first nonzero coordinate. "
                + "This is the unique normalized direction u whose quotient line coordinates agree on the two points. "
                + "Here line(u, x) records the nonpivot coordinates after subtracting the pivot coordinate of x times u. "
                + "The corresponding parallel classes partition the unordered edges and supply the basis assembly."))),
            DescribeRole.Theorem))));
}
