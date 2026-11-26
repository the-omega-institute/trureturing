using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class RoundQuaternionLocalPureScoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit rim potential has a cubic expansion with a uniform quartic remainder.",
        H("Pure Fourier rim scores"),
        Blocks(
            Paragraph(Text("RawRim is the quaternion-valued rim potential with a positive square-root real fibre. PureEstimates is the conjunction of the scalar identities, radicand and unit-norm bounds, the pure score lower bound, and the linearization identities used to add the second Fourier mode.")),
            Describe.Lean(DescribeId.Create("pure-score-estimates"),
                DeclarationHandle.Create(Prefix + "pure_score_estimates"), H("The pure-mode estimates"),
                StatementSource.FromAuthor(Disp(new Formula.Apply(
                    Seq(Operatorname, Grp(F.Id("PureEstimates"))),
                    [Seq(Operatorname, Grp(F.Id("RawRim")))]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the complex-pair score through degree three in the first Fourier amplitude. The constant score is one over the square root of three, the linear term vanishes, and the three quadratic terms coincide. Rationalization bounds the discarded terms in each quaternion factor. The product of their norm majorants bounds the tail of degree four and higher."))),
                DescribeRole.Theorem))));
}
