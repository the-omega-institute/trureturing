using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source graph constrains the hidden coordinate of the five-mode pyramid "
            + "and controls independent completion for every real observable.",
        H("Independent completion of actual three-terminal bond laws"),
        Blocks(
            Node("completion", "Independent base completion", DescribeRole.Definition,
                "For every p:Mode -> R, write X=p(ab)+p(all), Y=p(bc)+p(all), "
                    + "Z=p(ac) and q=XY/(1-Z). The completion in mode order "
                    + "separate,ab,bc,all,ac is (1-Z-X-Y+q,X-q,Y-q,q,Z). "
                    + "For a probability law with Z<1, its conditional base coordinates "
                    + "are independent and its three visible occupancies are X,Y,Z. "
                    + "The error estimates below use this definition only when Z<1; "
                    + "Z=1 is treated separately as the vertex law."),
            Node("interaction", "Observable interaction coefficient", DescribeRole.Definition,
                "For every real observable f:Mode -> R, interaction(f)="
                    + "f(separate)-f(ab)-f(bc)+f(all). The exceptional ac mode "
                    + "has zero coefficient because its mass is preserved."),
            Node("tree_pyramid", "The complete tree pyramid conclusion", DescribeRole.Theorem,
                "For every tree G with finite edge type, terminals a,b,c, "
                    + "and independent rates theta in [0,1], set p=bondLaw G a b c theta, "
                    + "X=p(ab)+p(all), Y=p(bc)+p(all), Z=p(ac), kappa=p(all). "
                    + "If Z<1, then |kappa-XY/(1-Z)| <= Z/(1-Z), and for every "
                    + "f:Mode -> R, the absolute difference between its expectations "
                    + "under p and completion(p) is at most |interaction(f)|Z/(1-Z). "
                    + "If Z=0, p equals completion(p) exactly. If Z=1, p assigns "
                    + "mass one to ac and zero to the other four modes. The proof "
                    + "uses the actual finite source normalization and nonnegativity, "
                    + "the full tree determinant bound and the identity "
                    + "kappa-XY/(1-Z)=delta(p)/(1-Z). The observable error equals "
                    + "interaction(f) times that hidden-mass error. No strict "
                    + "positivity of the five individual masses is required."),
            Node("pendant_pyramid", "The four-edge cactus pyramid conclusion", DescribeRole.Theorem,
                "For every u,v,s,A in [0,1], let p be the actual triangle-with-leaf "
                    + "source law. With the same X,Y,Z,kappa, Z<1 implies "
                    + "|kappa-XY/(1-Z)| <= 2Z/(1-Z), and every real observable's "
                    + "expectation error is at most 2|interaction(f)|Z/(1-Z). "
                    + "Z=0 gives exact completion and Z=1 gives the ac vertex law. "
                    + "This applies to the entire four-edge rate family, including "
                    + "the sharp family. The arbitrary-cactus graph reduction and "
                    + "general block-rank constants remain outside this theorem.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-completion-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
