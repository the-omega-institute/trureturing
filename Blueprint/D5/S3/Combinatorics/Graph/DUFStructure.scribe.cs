using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFStructure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of an arbitrary finite vertex type with n vertices. The definitions apply to every such H; three-uniformity, DUF, and the cap are assumptions only where stated. Unordered pairs range over the whole ground set, so absent pairs are included. The pair extension relation is directed; a common link is obtained by transposing that relation.",
        H("Disjoint-union uniqueness and intersecting links"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pairs"),
                DeclarationHandle.Create(Prefix + "pairs"),
                H("All ground pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ground pairs are all two-element subsets of the finite vertex type. Their number is binom(n,2), independently of which pairs occur in H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("duf"),
                DeclarationHandle.Create(Prefix + "DUF"),
                H("Uniqueness of disjoint unions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Whenever A, B, C, and D belong to H, A and B are disjoint, C and D are disjoint, and their unions agree, either A=C and B=D or A=D and B=C."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("neighbors"),
                DeclarationHandle.Create(Prefix + "neighbors"),
                H("Exact neighborhoods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("N(p) consists of vertices x outside p for which inserting x into p gives a member of H. For pairs in a triple family, uniformity already excludes vertices of p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common"),
                DeclarationHandle.Create(Prefix + "common"),
                H("Common links"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("K(q) consists of ground pairs p such that q is contained in N(p). The containment goes in this direction and is not asserted to be symmetric."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber"),
                DeclarationHandle.Create(Prefix + "fiber"),
                H("Exact neighborhood fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("F(S) consists of all ground pairs whose neighborhood is exactly S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("capfour"),
                DeclarationHandle.Create(Prefix + "CapFour"),
                H("Maximum pair codegree four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ground pair, including every absent pair, has at most four neighbors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("star"),
                DeclarationHandle.Create(Prefix + "star"),
                H("Stars"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write cA for the star with center c and leaf set A, consisting of the sets {c,x} for x in A. The definition permits any c and A; the structural conclusions explicitly exclude c from A, so their star edges are two-element sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("intersecting"),
                DeclarationHandle.Create(Prefix + "Intersecting"),
                H("Intersecting edge families"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every two members of the edge family have nonempty intersection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("intersecting-classification"),
                DeclarationHandle.Create(Prefix + "intersecting_classification"),
                H("Star or triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonempty finite intersecting family of two-element sets is a star or the full pair family on a three-element set. In the star case the center is outside its leaf set and the number of leaves equals the number of edges. A singleton edge may have either endpoint as center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-intersecting"),
                DeclarationHandle.Create(Prefix + "common_intersecting"),
                H("The forbidden common-link matching"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and every two-element set q, K(q) is intersecting. Two disjoint common-link edges would give two unequal unordered decompositions of the same union into members of H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("duf-iff-common-intersecting"),
                DeclarationHandle.Create(Prefix + "duf_iff_common_intersecting"),
                H("Equivalence for triple families"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a three-uniform family, DUF is equivalent to every two-vertex common link being intersecting. In the reverse direction, unequal decompositions of a six-element union give a two-plus-one intersection pattern and hence a disjoint pair of common-link edges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-structure"),
                DeclarationHandle.Create(Prefix + "common_structure"),
                H("Four-edge common links"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and CapFour, every two-element set q has card(K(q))<=4. If card(K(q))=4, there are a center c and a four-element set S with c outside both q and S, K(q)=cS, and N({c,u})=S for every u in q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiber-structure"),
                DeclarationHandle.Create(Prefix + "fiber_structure"),
                H("Four-neighborhood fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and CapFour and each four-element set S, F(S) is intersecting and has at most four edges. If F(S) is nonempty, either F(S)=cA with c outside A and S, A disjoint from S, card(A)=card(F(S)), and A contained in N({c,s}) for every s in S, or F(S) is the full pair family on a three-element set."))),
                DescribeRole.Theorem)),
        []));
}
