using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class TriangleDefectStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/TriangleDefectStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle defects count anchored disagreements and are bounded by every potential's edge errors.",
        H("Triangle Defects and Potential Errors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("edge-defects"),
                DeclarationHandle.Create(Prefix + "edgeDefects"),
                H("Anchored edge disagreements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an edge label a and anchor r, E(r) counts all ordered pairs (i,j) "
                    + "for which a(i,j) differs from a(r,j)-a(r,i). Repeated vertices are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("triangle-defects"),
                DeclarationHandle.Create(Prefix + "triangleDefects"),
                H("Oriented triangle defects"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "T counts all ordered triples (r,i,j) for which "
                    + "a(r,i)+a(i,j)+a(j,r) is nonzero, including repeated vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("potential-errors"),
                DeclarationHandle.Create(Prefix + "potentialErrors"),
                H("Potential edge errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Err(p) counts ordered pairs (i,j) with a(i,j) different from p(j)-p(i). "
                    + "Diagonal pairs are included in the count."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("triangle-defect-stability"),
                DeclarationHandle.Create(Prefix + "triangle_defects_incidence_repair_and_error_bound"),
                H("Incidence and universal potential error bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("r"), Sp, InMacro, Sp, F.Id("V")), Sp,
                    F.Id("E"), Open, F.Id("r"), Close, Sp, Eq, Sp, F.Id("T"),
                    Quad, Land, Quad, Exists, Sp, F.Id("r"), Sp, InMacro, Sp, F.Id("V"),
                    Comma, Sp, F.Id("n"), F.Id("E"), Open, F.Id("r"), Close,
                    Sp, Leq, Sp, F.Id("T"), Quad, Land, Quad,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("T"), Sp, Leq, Sp,
                    D(3), Open, F.Id("n"), Minus, D(2), Close,
                    F.Id("Err"), Open, F.Id("p"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a nonempty finite vertex type, A any additive commutative group, "
                        + "and a an edge labeling with a(i,i)=0 and a(j,i)=-a(i,j) for all vertices. "
                        + "Write n for the number of vertices. The exact ordered incidence identity "
                        + "sum_r E(r)=T holds, an anchor r has n E(r)<=T, and every potential p "
                        + "satisfies T<=3(n-2)Err(p), with natural-number subtraction. No division is used.")),
                    Paragraph(Text(
                        "A defective triangle has an erroneous edge for every p. Repeated-vertex "
                        + "triangles vanish by alternation. For distinct triples, each erroneous "
                        + "ordered edge occurs in three cyclic positions and has n-2 choices "
                        + "for the third vertex. The proof also selects a minimum E(r). "
                        + "The result includes n=1,2 and groups with 2-torsion."))),
                DescribeRole.Theorem))));
}
