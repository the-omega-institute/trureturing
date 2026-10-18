using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalTriangleArmsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalTriangleArms.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete central triangle and three-arm bond source has a constant-two "
            + "determinant bound on the closed six-dimensional probability cube.",
        H("A central triangle with three independent arms"),
        Blocks(
            Node("triangleArmsEnds", "The actual six-edge network", DescribeRole.Definition,
                "The three terminals are 0,1,2 and the central ports are 3,4,5. "
                    + "The six edges in order are (3,4),(4,5),(3,5),(0,3),(1,4),(2,5), "
                    + "with independent opening rates u,v,s,A,B,C."),
            Node("triangle_arms_law", "The full five-mode source law", DescribeRole.Theorem,
                "For all real u,v,s,A,B,C, put U=u+(1-u)sv, V=v+(1-v)us, "
                    + "W=s+(1-s)uv and K=uv+us+vs-2uvs. The actual law p of the "
                    + "six-edge network, in mode order separate,ab,bc,all,ac, is "
                    + "(1-ABU-BCV-ACW+2ABCK, ABU-ABCK, BCV-ABCK, ABCK, ACW-ABCK). "
                    + "All sixty-four open subgraphs are classified by actual reachability "
                    + "before their independent product weights are summed. Thus the "
                    + "formula preserves the whole partition law, including its joint "
                    + "all-connected event, rather than just pair marginals."),
            Node("triangle_arms_factorization", "The complete arm transformation", DescribeRole.Theorem,
                "For all real u,v,s,A,B,C, put K=uv+us+vs-2uvs, "
                    + "L=(1-s)(u+v-uv), Z0=s(1-u)(1-v), S=AC and let p be the "
                    + "actual six-edge law. Then p(ac)=S[Z0+(1-B)K] and "
                    + "delta(p)=B^2*S*Z0*[L+(1-S)K]+B(1-B)SK[1-S(Z0+K)]. "
                    + "Both identities hold without divisions and retain deterministic "
                    + "arms and every zero-mass boundary."),
            Node("triangle_arms_bound", "Uniform constant two for all arms", DescribeRole.Theorem,
                "For all u,v,s,A,B,C in [0,1], the actual six-edge law p satisfies "
                    + "0 <= delta(p) <= 2p(ac). Here K,L,Z0,S are nonnegative, "
                    + "S<=1, Z0+K=s+(1-s)uv<=1 and L+(1-S)K<=2. The first "
                    + "term of the arm factorization is at most 2SZ0 and the second "
                    + "is at most (1-B)SK. Their sum is at most 2S[Z0+(1-B)K]."),
            Paragraph(Text(
                "To obtain the universal cactus theorem, one must still prove that "
                    + "every source cactus has a central triangle and three independent "
                    + "effective arms preserving this complete five-mode law. This "
                    + "module supplies the target network and all-rate bound; it does "
                    + "not assume or prove that graph reduction."))),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-triangle-arms-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
