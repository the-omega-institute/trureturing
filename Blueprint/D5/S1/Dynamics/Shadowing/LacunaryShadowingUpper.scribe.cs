using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LacunaryShadowingUpperDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed finite set traces every pseudo-orbit", H("One fixed finite set traces every pseudo-orbit"), Blocks(
        Paragraph(Text("The explicit phase masks repair every natural-time pseudo-orbit, preserving its observed windows and the common initial window.")),
        Describe.Lean(DescribeId.Create("lacunary-neighborhood-upper"), DeclarationHandle.Create(Owner + "lacunary_neighborhood_upper"), H("Neighborhood (m-1)-shadowing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each accuracy choose a finite signed window using the genuine compatible product metric. The phase-cover theorem constructs a scale K and m-1 masks. A sufficiently accurate pseudo-orbit has a signed diagonal agreeing with each observed window, including the negative initial coordinates. Short progression constraints already hold in this diagonal; long constraints become legal after masking because no mask retains three vertices. All masked whole configurations belong to X_m. Their single finite set has cardinality at most m-1 and initial diameter below the prescribed accuracy. At every natural time one of these same configurations preserves the entire current window. No supplied mask-existence or tracing-count assumption remains in the theorem."))), DescribeRole.Theorem))));
}
