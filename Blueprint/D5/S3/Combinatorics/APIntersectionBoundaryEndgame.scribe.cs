using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class APIntersectionBoundaryEndgameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary families with one common avoider difference satisfy the pair-count bound.",
        H("Boundary Arithmetic-Progression Intersection Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/APIntersectionBoundaryEndgame.result"),
            H("At most one more member than unordered pairs"),
            StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For positive d and a family F of subsets of [1,N], suppose distinct members intersect "
                + "in nonempty arithmetic progressions, members of size at least four are arithmetic "
                + "progressions, and members avoiding 1 have at least four terms and difference d. "
                + "Then |F| is at most C(N,2)+1. Code each member by a point of [2,N], a pair "
                + "from [2,N], or one extra value. The code is injective: equal extra codes, equal "
                + "point codes, and equal pair codes are excluded. For pair codes, the six "
                + "unordered cases are triple with triple, triple with longer boundary progression, "
                + "triple with avoider, two longer boundary progressions, longer boundary "
                + "progression with avoider, and two avoiders."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs"))]));
}
