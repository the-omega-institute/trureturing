using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class GoldenBeattyCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The golden shift s(v)=floor((v+1)/phi) satisfies s(v)<=N exactly when v<floor((N+1)phi), so the count of such v is floor((N+1)phi).",
        H("Golden Beatty Count"),
        Blocks(
            Describe.Lean(DescribeId.Create("golden-beatty-count"),
                DeclarationHandle.Create("D5/S1/Phase/GoldenBeattyCount.golden_beatty_count"),
                H("The golden shift threshold is a Beatty floor"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Lfloor, Frac, Grp(F.Id("v"), Plus, D(1)), Grp(Phi), Rfloor,
                                    Sp, Le, Sp, F.Id("N"),
                                    Sp, Iff, Sp,
                                    F.Id("v"), Sp, Lt, Sp,
                                    Lfloor, Open, F.Id("N"), Plus, D(1), Close, Phi, Rfloor))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For the golden shift s(v) = floor((v+1)/phi), the theorem proves the membership "
                                        + "equivalence s(v) <= N iff v < floor((N+1)*phi). Since the natural numbers v with "
                                        + "s(v) <= N are then exactly {0, 1, ..., floor((N+1)*phi) - 1}, their count is exactly "
                                        + "floor((N+1)*phi).")),
                                    Paragraph(Text(
                                        "The proof is elementary: the floor threshold unfolds to (v+1)/phi < N+1, hence "
                                        + "v+1 < (N+1)*phi, and the irrationality of (N+1)*phi (as a nonzero natural multiple "
                                        + "of the golden ratio) upgrades the strict real inequality to v+1 <= floor((N+1)*phi), "
                                        + "i.e. v < floor((N+1)*phi). No Beatty complementarity beyond this count is asserted."))),
                DescribeRole.Theorem))));
}
