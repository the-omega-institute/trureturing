using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CfmEndpointPositivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CfmEndpointPositivity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sandwich derivative applied to a resolvent increment is positive at both endpoints.",
        H("Positivity at both endpoints"),
        Blocks(Describe.Lean(
            DescribeId.Create("cfm-endpoint-derivatives-positive"),
            DeclarationHandle.Create(Module + ".endpoint_derivatives_positive"),
            H("The two endpoint derivatives are positive semidefinite"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For ordered complex Hermitian 3 by 3 matrices U≤V with −I<U,V<I, "
                    + "set ε=1/20000 and g(X)=R_2(X)+R_3(X)−εR_4(X). Then "
                    + "Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite.")),
                Paragraph(Text("Factor every increment at the selected endpoint C as R_s(C) Z_s R_s(C), "
                    + "with H/3≤Z_s≤3H and H=V−U. Expand the nine terms of Dg_C(g(V)−g(U)). "
                    + "The four positive terms indexed by 2 and 3 contribute at least one third of "
                    + "the three unmixed H-quadratic forms. The 4,4 term is nonnegative. The four negative "
                    + "mixed terms are bounded below by −6ε times the two mixed forms. The three-node "
                    + "estimate bounds those by 54 times the unmixed forms. The remaining coefficient "
                    + "is 1/3−324ε=4757/15000>0. Singular H and repeated eigenvalues are included."))),
            DescribeRole.Theorem))));
}
