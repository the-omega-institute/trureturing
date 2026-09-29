using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class ThreeTorsionZModDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-torsion subgroup of the cyclic modulus 3m has three elements.",
        H("Three-Torsion Coordinates Modulo 3m"),
        Blocks(
            Paragraph(Text("The modulus is 3m with m a positive natural number. "
                + "All equalities in the displayed statement are in ZMod(3m).")),
            Describe.Lean(DescribeId.Create("three-torsion-zmod-characterization"),
                DeclarationHandle.Create("D5/S3/Factorization/ThreeTorsionZMod.three_nsmul_eq_zero_iff"),
                H("Exact three-torsion coordinates"),
                StatementSource.FromAuthor(Disp(Seq(D(3), F.Id("x"), Sp, Eq, Sp, D(0),
                    Sp, Iff, Sp, F.Id("x"), Sp, InMacro, Sp, OpenBrace,
                    D(0), Comma, Sp, F.Id("m"), Comma, Sp, D(2), F.Id("m"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a representative in [0,3m), the equation "
                    + "3x=0 is equivalent to m dividing that representative. "
                    + "The only possibilities are 0, m, and 2m."))), DescribeRole.Theorem))));
}
