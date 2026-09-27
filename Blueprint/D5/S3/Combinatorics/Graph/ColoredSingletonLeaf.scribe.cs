using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ColoredSingletonLeafDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ColoredSingletonLeaf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let G be a simple graph on a finite vertex type V, and let c:V->Fin(3) be a proper coloring: adjacent vertices have different colors. Write A_i={x:c(x)=i} and B=sum_i 1/(card(A_i)+1)+(1/2)sum_x 1/(degree_G(x)+1), with rational arithmetic. All three colors are included in the first sum, and every vertex, including each isolated vertex, is included in the second sum.",
        H("Reciprocal estimates for singleton color leaves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-leaf-reciprocal-bound"),
                DeclarationHandle.Create(Prefix + "singleton_leaf_reciprocal_bound"),
                H("One singleton leaf and the exact neighbor correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose w,l,z have pairwise distinct colors, A_c(l)={l}, N_G(l)={w}, and N_G(w)={l,z}. Put k=card(A_c(w))-1 and h=degree_G(z). Then B>=23/12+k/[2(k+1)(k+2)]+1/[2(h+1)]. The graph has arbitrary finite size. No positive lower degree assumption is imposed on its other vertices.")),
                    Paragraph(Text("Let U=A_c(w)\\{w} and Z=A_c(z), with card(U)=k and card(Z)=r>=1. A vertex of U cannot meet its own color or l, so its neighborhood lies in Z and its degree is at most r. A vertex of Z\\{z} cannot meet its own color, l, or w, so its neighborhood lies in U and its degree is at most k. The degrees of w and l are exactly two and one; the degree of z remains h.")),
                    Paragraph(Text("Partitioning the actual vertex sum gives B>=11/12+1/(k+2)+(k+2)/[2(r+1)]+(r-1)/[2(k+1)]+1/[2(h+1)]. The first four terms equal 11/12+phi(k,r)+k/[2(k+1)(k+2)], where phi(k,r)=(k+2)/[2(r+1)]+r/[2(k+1)]. Since k and r are integers, either r<=k or r>=k+1. Thus phi(k,r)-1=(r-k)(r-k-1)/[2(k+1)(r+1)]>=0, giving the claimed bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-singleton-leaves-internal-payment"),
                DeclarationHandle.Create(Prefix + "two_singleton_leaves_internal_payment"),
                H("Two singleton leaves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same hypotheses, suppose also A_c(z)={z} and N_G(z)={w}. Put d=card(A_c(w))+1. Then B=d/2+2/3+1/d and B>=13/6.")),
                    Paragraph(Text("Every vertex outside {w,l,z} lies in the color class of w. Properness excludes neighbors of that color, while the singleton neighborhoods of l and z exclude both other colors. Hence every such vertex is isolated. There are d-2 of them, and the remaining degrees are two, one, and one. The color contribution is 1+1/d, and the vertex contribution is (1/2)(d-2+1/3+1/2+1/2), proving the identity. Since d>=2, its excess above 13/6 equals (d-1)(d-2)/(2d)>=0."))),
                DescribeRole.Theorem))));
}
