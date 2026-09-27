using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseEqualityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseEqualityRegistrations"),
        Blocks(
            Node("substitutionArena", "The three substitution labels remain the states; both outputs are codes in Fin 3.", DescribeRole.Definition),
            Node("substitutionRealization", "Both readouts return the label code: zero denotes [large], one [large, small], and two [large, combined].", DescribeRole.Definition),
            Node("substitution_bridge", "Encoding and reconstruction are checked separately for both original substitution expressions at every label. Code equality is equivalent to list equality on their occurring support; no injection on all lists is asserted.", DescribeRole.Theorem),
            Node("substitution_lawSensitive", "The frozen compatibility theorem satisfies the code law through the bridge; constant codes zero and one falsify it.", DescribeRole.Theorem),
            Node("substitution_slotSensitive", "Distinct Fin 3 codes zero and one witness independent sensitivity of both readout slots.", DescribeRole.Theorem),
            Node("recenterReadout", "The constant Fin 2 zero code represents the integer origin for every direction; the same definition is used in the realization and declared readout.", DescribeRole.Definition),
            Node("recenterArena", "The three directed neighbors remain the states, with Fin 2 output codes.", DescribeRole.Definition),
            Node("recenterRealization", "Both readouts use the zero code for the recentered neighbor and the integer origin.", DescribeRole.Definition),
            Node("recenter_bridge", "The bridge checks encoding and reconstruction of every recentered direction from the definitions. Zero decodes to (0, 0) and one to (1, 0); equality is transported on the occurring support without a global injection from integer pairs or use of the registered theorem.", DescribeRole.Theorem),
            Node("recenter_lawSensitive", "The frozen recenter theorem satisfies the code law through the bridge; distinct constant codes zero and one falsify it.", DescribeRole.Theorem),
            Node("recenter_slotSensitive", "The unused Fin 2 code one and origin code zero witness independent sensitivity of both readout slots.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseEqualityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
