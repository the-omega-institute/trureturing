using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class FinitePhaseCoboundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Dynamics/FinitePhaseCoboundary.";

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Identity return transport on a finite cyclic phase tower gives a continuous transfer.",
            H("Continuous coboundaries from finite phase towers"),
            Blocks(
                Paragraph(Text("Let a continuous integer action admit a continuous cyclic phase of positive height h. A continuous group-valued cocycle whose ordered h-step product is one at every phase-zero point has a continuous transfer b with b(Tx) = c(x)b(x), normalized to one on the zero phase. At a point of phase r, move back r steps to the tower base and multiply the intervening cocycle values on the left. Local constancy of the phase proves continuity; identity return transport handles the tower wrap. The target may be a noncommutative topological group. Compactness, minimality and finite target groups are unnecessary.")),
                Paragraph(Text("The ordered product reuses SkewGroupHolonomy in the opposite group. This is a general return-to-coboundary bridge, rather than a claim that a particular symbolic system has identity returns. Such an application must separately supply its actual phase map, continuity, equivariance and return identity. No literature-priority claim is made.")),
                Node("left-holonomy", "leftHolonomy", "Left ordered transport",
                    "The product P starts at one and obeys P(n+1,x) = c(T^n x) P(n,x). Reversing multiplication through the opposite group preserves the order for noncommutative targets.", DescribeRole.Definition),
                Node("phase-return-transfer", "exists_continuous_transfer_of_phase_return",
                    "Identity return gives a continuous transfer",
                    "For every positive cyclic phase height and continuous equivariant phase, identity full return transport on the zero phase yields a continuous normalized solution of b(Tx) = c(x)b(x)."))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
