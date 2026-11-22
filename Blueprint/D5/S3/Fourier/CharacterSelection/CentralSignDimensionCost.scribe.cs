using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class CentralSignDimensionCostDocument : IScribeDocumentDefinition
{
    private static readonly Formula K = F.Id("k"), M = F.Id("m"), R = F.Id("r"), J = F.Id("j");
    private static readonly Formula Degree = Seq(F.Id("d"), Underscore, J);
    private static readonly Formula Cost = Seq(D(1), Plus, R, Plus, Sum, Underscore, J, Sp, Degree, Caret, D(2));
    private static readonly Formula Bound = Seq(D(4), K, Plus, D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint separation of a binary cube places a sharp lower bound on the sum of squares of channel dimensions.",
        H("Dimension cost of separating central signs"),
        Blocks(Describe.Lean(DescribeId.Create("central-sign-cost"),
            DeclarationHandle.Create("D5/S3/Fourier/CharacterSelection/CentralSignDimensionCost.central_sign_dimension_cost"),
            H("The cost bound and its equality case"),
            StatementSource.FromAuthor(Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, K, Sp, Le, Sp, M,
                Comma, Sp, Cost, Sp, Ge, Sp, Bound, RowBreak, Amp, Cost, Eq, Bound,
                Sp, Leftrightarrow, Sp, M, Eq, K, Comma, R, Eq, D(0), Comma,
                Sp, Forall, Sp, J, Comma, Degree, Eq, D(2), Comma, Sp, SigmaLower,
                Sp, F.Text, Grp(F.Id("bijective")), End, Grp(F.Id("aligned"))))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The complete binary profile of each k-bit string consists of r constant readings of dimension one and m further readings of integer dimensions at least two. Include one distinguished trivial channel of dimension one. If the complete profile separates all strings, the remaining profile σ alone is injective. Hence its codomain of size 2ᵐ contains at least 2ᵏ values. Each squared dimension costs at least four, and a dimension above two contributes strictly more. At equality there are no additional one-dimensional channels, every remaining dimension is two, and σ is a bijection of equally large cubes. In the compact-group application, the commutator condition is what makes the one-dimensional central restrictions constant."))),
            DescribeRole.Theorem))));
}
