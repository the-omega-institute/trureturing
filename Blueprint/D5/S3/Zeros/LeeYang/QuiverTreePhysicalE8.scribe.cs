using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class QuiverTreePhysicalE8Document : IScribeDocumentDefinition
{
    private const string PhysicalPrefix = "D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-vertex physical tree Lee-Yang claim has an eight-edge counterexample at tau=-1.",
        H("An all-vertex physical tree polynomial with off-circle roots"),
        Blocks(
            PhysicalNode("deg", "The number of endpoint incidences", Op("deg"),
                "For finite edge type E, deg src tgt v counts every source and target incidence. "
                + "On the explicit witness the degrees are (2,4,4,1,1,1,1,1,1)."),
            PhysicalNode("fEnd", "Endpoint factorial factor", Op("fEnd"),
                "For a natural number a, fEnd a = (2a)!/((a−1)!a!), with real casts and "
                + "natural subtraction. This is the endpoint factor from (2.15) on the positive split domain."),
            PhysicalNode("cVert", "Vertex factorial ratio", Op("cVert"),
                "For natural d and α, cVert d α = (d−1)!/(d−α+2)!, with real casts and "
                + "natural subtraction. It is the remaining vertex factor in (2.15)."),
            PhysicalNode("physRho", "The all-vertex physical split weight", Op("physRho"),
                "physRho is the unfactorized product over every edge and every vertex: edge binomials, "
                + "all cVert factors, and the actual fEnd factors at both endpoint incidences. Frozen mass, "
                + "splits and treePoly are reused; source and target follow the frozen orientation convention."),
            PhysicalNode("claim", "The all-vertex physical FMR-P claim", Op("claim"),
                "This closed proposition quantifies over finite named spanning trees with at least two edges, "
                + "all edge totals at least two, and the physical weight physRho at τ=−1. It asserts that every "
                + "complex root of the frozen tree polynomial has norm one. It uses the all-vertex (2.19) "
                + "reading; the shorter printed (2.31) expression remains distinct."),
            PhysicalNode("result", "The all-vertex physical FMR-P claim is false",
                Seq(Neg, Sp, Op("claim")),
                "The explicit nine-vertex, eight-edge witness has all totals equal to three. The proof retains "
                + "all 256 complementary splits and all 512 spin states per split, keeps all nine actual cVert "
                + "factors, proves the exact physical normalization (360⁸·36/512), and reduces to the reciprocal "
                + "polynomial certificate with a nonreal root. Reciprocal lifting yields roots inside and outside "
                + "the unit circle, so this is a literal closed refutation of the exact physical claim. The readable "
                + "automorphism factor 72 and source prefactor 120⁸/4 are correspondence only; the kernel result "
                + "uses the proved nonzero normalization. No claim is made about printed (2.31), an erratum, author "
                + "intent, priority, other τ, the full tree ensemble or Conjecture 2.", true))));

    private static DocumentBlock PhysicalNode(string name, string title, Formula formula, string prose,
        bool theorem = false) => Describe.Lean(
            DescribeId.Create("quiver-tree-physical-e8-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(PhysicalPrefix + name), H(title),
            theorem ? StatementSource.FromAuthor(Disp(formula)) : StatementSource.WithoutFormula(),
            theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(DefinitionDsl.Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
