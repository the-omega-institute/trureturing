using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterTwistedOctonionNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit signed Cayley-Dickson table has a multiplicative Euclidean norm.",
        H("Auxiliary Twisted Octonion Norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("auxiliary-twisted-octonion-norm"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.norm_mul"),
                H("The signed multiplication has a composition norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Operatorname, Grp(F.Id("normSq")), Open,
                    F.Id("mul"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Close,
                    Eq, Sp, Operatorname, Grp(F.Id("normSq")), Open, F.Id("x"), Close,
                    Times, Operatorname, Grp(F.Id("normSq")), Open, F.Id("y"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Lean definition is the explicit eight-coordinate signed Cayley-Dickson table. "
                        + "The proof expands every coordinate and normalizes the resulting polynomial identity over the reals.")),
                    Paragraph(Text(
                        "The companion unit lemmas are checked from the same table. This is an auxiliary "
                        + "twisted group-algebra model and does not assert a VOA or Monster OPE construction."))),
                DescribeRole.Theorem))));
}
