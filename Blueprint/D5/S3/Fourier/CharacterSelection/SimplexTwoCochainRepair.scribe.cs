using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class SimplexTwoCochainRepairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tetrahedral defects count anchored triangle repairs and detect exact edge cochains.",
        H("Degree-Two Simplex Cochain Repair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("face-errors"),
                DeclarationHandle.Create(Prefix + "faceErrors"),
                H("Anchored triangle errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an ordered triangle cochain F and vertex r, E(r) counts triples "
                    + "(i,j,k) for which F(i,j,k) differs from "
                    + "F(r,j,k)-F(r,i,k)+F(r,i,j). Repeated vertices are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tetra-defects"),
                DeclarationHandle.Create(Prefix + "tetraDefects"),
                H("Tetrahedral defects"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "T counts ordered quadruples (r,i,j,k) for which "
                    + "F(i,j,k)-F(r,j,k)+F(r,i,k)-F(r,i,j) is nonzero. "
                    + "Repeated vertices are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-errors"),
                DeclarationHandle.Create(Prefix + "edgeErrors"),
                H("Edge-cochain triangle errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any edge cochain a, Err(a) counts ordered triples (i,j,k) for "
                    + "which F(i,j,k) differs from a(j,k)-a(i,k)+a(i,j). "
                    + "Repeated vertices are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-cochain-repair"),
                DeclarationHandle.Create(Prefix + "tetra_defects_incidence_repair_and_exactness"),
                H("Incidence, repair, and exactness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("r"), Sp, InMacro, Sp, F.Id("V")), Sp,
                    F.Id("E"), Open, F.Id("r"), Close, Sp, Eq, Sp, F.Id("T"),
                    Quad, Land, Quad, Open, Exists, Sp, F.Id("r"), Sp, InMacro, Sp, F.Id("V"),
                    Comma, Sp, F.Id("n"), F.Id("E"), Open, F.Id("r"), Close,
                    Sp, Leq, Sp, F.Id("T"), Close, Quad, Land, Quad,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("T"), Sp, Leq, Sp,
                    D(4), F.Id("n"), F.Id("Err"), Open, F.Id("a"), Close, Close,
                    Quad, Land, Quad, Open,
                    Open, F.Id("dF"), Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
                    Open, Exists, Sp, F.Id("a"), Comma, Sp, F.Id("F"), Sp, Eq, Sp,
                    F.Id("da"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a nonempty finite vertex type, A an additive commutative group, "
                        + "and F any ordered triangle cochain with values in A. Write n for the "
                        + "number of vertices. The sum of anchored errors E(r) equals the total "
                        + "tetrahedral defect count T, and some anchor has n E(r) at most T. "
                        + "For every edge cochain a, T is at most 4n Err(a).")),
                    Paragraph(Text(
                        "A defective tetrahedron has an erroneous face for every a. Each "
                        + "ordered face occurs in n tetrahedra in each of four positions. "
                        + "The tetrahedral defect vanishes at every ordered quadruple exactly "
                        + "when an edge cochain a satisfies "
                        + "F(i,j,k)=a(j,k)-a(i,k)+a(i,j) at every ordered triple. "
                        + "In that direction a(i,j)=F(r,i,j) for any fixed anchor r. "
                        + "No alternating condition on F or torsion condition on A is needed."))),
                DescribeRole.Theorem))));
}
