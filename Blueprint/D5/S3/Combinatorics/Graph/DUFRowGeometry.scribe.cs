using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFRowGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local graphs and owned triangle rows",
        H("Local graphs and owned triangle rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/DUFRowGeometry.result"),
                H("Local graphs and owned triangle rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A family H consists of finite subsets of a finite ambient type V. The disjoint-union-free condition says that two disjoint pairs of members with the same union agree up to exchanging the pair. For a triple e in H, the local vertices are pairs (a,x), where a belongs to e, x lies outside e, and replacing a by x gives another member of H. Two local vertices (a,x) and (b,y) are adjacent when a differs from b, x differs from y, and replacing both a and b by x and y gives a member of H. The color is the coordinate a, identified with one of three colors.")),
                    Paragraph(Text("The graph and finite-set descriptions agree exactly: equal colors mean equal first coordinates, graph neighborhoods map bijectively to localNeighbors, and graph degree equals the cardinality of that finite neighborhood. Mixedness means that two neighbors have different first coordinates. For an actual member of a DUF family, every mixed vertex has degree two. The graph potential equals its reciprocal weight: the sum over the three colors of the reciprocal of class size plus one, together with half the sum over vertices of the reciprocal of degree plus one. An adjacent vertex l has degree one precisely when its neighborhood is the singleton containing its neighbor w.")),
                    Paragraph(Text("A row consists of a pair q, a triple T, and a chosen element i of q. Validity requires common(H,q) to be exactly the three pairs in T. Then q and T are disjoint. The three row members are the triples obtained by adjoining i to a pair in T; each is an actual member of H and has the stated packet representation. Write j for the other element of q. The assigned local vertex is (i,j); it exists on each row member, is mixed when H is DUF, and determines the entire valid row uniquely.")),
                    Paragraph(Text("A mark b is an element of T for which neighbors(H,{i,b}) equals T minus {b}, and common(H,T minus {b}) equals the pairs {k,b} with k in q. Its recipient is the row member obtained by adjoining i to T minus {b}. The internal group is the union, over the actual marks, of the other two row members. It is a subset of the row. With no marks it is empty; with one mark it has exactly two members and excludes the recipient; with at least two marks it is the whole row. In the one-mark case the group is also the image of T minus {b} under the recipient map.")),
                    Paragraph(Text("Every internal member has a unique packet owner: any packet representation has the same q, T and i. Consequently the internal groups of distinct valid rows are disjoint. The proof extracts the five distinct vertices of the marked endpoint from an actual internal member and applies endpoint ownership to that representation.")),
                    Paragraph(Text("Finally suppose an actual local graph has a mixed vertex w adjacent to a degree-one vertex l whose entire color class is {l}. There is a valid row r and an actual mark b such that e belongs to its internal group, e has its packet representation, and w is its assigned vertex. The two mark equalities hold literally. The construction identifies five distinct ambient vertices, reconstructs the common-link triangle, and uses the singleton color class to determine the complete neighbor set. Thus the row is obtained from the actual local configuration, without a row-selection assumption."))),
                DescribeRole.Theorem))));
}
