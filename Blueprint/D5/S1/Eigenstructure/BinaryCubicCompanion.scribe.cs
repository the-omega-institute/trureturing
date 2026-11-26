using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class BinaryCubicCompanionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both trace-zero cubic polynomials with constant term one give a companion basis over the binary field.",
        H("Companion bases over the binary field"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-cubic-companion-basis"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/BinaryCubicCompanion.exists_basis"),
            H("Two cubic companion cases"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Let f act on a three-dimensional vector space over the binary field. For characteristic polynomial X cubed plus a times X plus one, there is an ordered basis b0, b1, b2 with f b0 equal to b1, f b1 equal to b2, and f b2 equal to b0 plus a times b1.")),
                Paragraph(Text("Cayley–Hamilton gives the cubic recurrence. The kernels of f minus the identity and f squared plus f plus the identity are proper. A vector outside both kernels is nonzero and gives a cyclic basis by the recurrence and linear independence over the binary field.")),
                Paragraph(Text("These companion matrices are the final two representatives in the Heawood double cover classification. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108"))),
            DescribeRole.Theorem))));
}
