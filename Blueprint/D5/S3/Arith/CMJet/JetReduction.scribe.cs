using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetJetReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/JetReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient reduction on the curve extends to both polynomial variables.",
        H("Reduction of the integer lemniscatic section jets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jet-reduction-deriv"),
                DeclarationHandle.Create(Prefix + "jetReduction_deriv"),
                H("Reduction commutes with differentiation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient derivative and the ordinary polynomial derivative both commute with the lifted ring homomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("jet-reduce-cast"),
                DeclarationHandle.Create(Prefix + "jet_reduce_cast"),
                H("Exact residue of every integer jet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The section, all derivative orders, and evaluation commute with reduction, for every modulus."))),
                DescribeRole.Theorem)
        )));
}
