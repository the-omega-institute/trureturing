using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitCoefficientExchangeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One coefficient acts in its own sector of a stable submodule of alternating forms.",
        H("Exchanging a Coefficient Sector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coefficient-family-exchange"),
                DeclarationHandle.Create(Module + ".coefficient_family_exchange"),
                H("Exchanging a Coefficient Sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use alternating forms of degree d in a common integral basis with ordered index "
                    + "set I. Fix a finite subset A of I, a selected d-element subset F of I and a "
                    + "finite family of prior d-element subsets of I. The projection keeps precisely "
                    + "the coefficients indexed by d-element subsets G with G intersect A equal to "
                    + "F intersect A. Assume the projection preserves the submodule K of forms and "
                    + "each prior subset has a different intersection with A from F. "
                    + "Let P be the common kernel of all prior coefficient readouts in K, and let "
                    + "Q be the kernel of the F readout in K. There is an integer-linear isomorphism "
                    + "from K times the intersection of P and Q to P times Q. "
                    + "Exchange the complementary sector of two forms while holding the selected "
                    + "sector of each form in place."
                    + " This operation is an integral linear involution."
                    + " Each prior coefficient reads the exchanged part, while the new coefficient reads the part held in place."
                    + " The unrestricted and jointly restricted modules therefore have the same "
                    + "product as the two separately restricted modules."))),
                DescribeRole.Theorem))));
}
