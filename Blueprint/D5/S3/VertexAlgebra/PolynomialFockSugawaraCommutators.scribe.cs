using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockSugawaraCommutatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/kytola2025virasoro");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete polynomial Fock modes satisfy the Heisenberg and Sugawara-current relations.",
        H("Polynomial Fock Mode Commutators"),
        Blocks(
            Paragraph(Text("The modes and pointwise finite Sugawara operators are those of "
                + "Polynomial Fock Sugawara Support. The generic Sugawara proof of Kytola "
                + "supplies a reference for the commutator calculation; the concrete "
                + "Heisenberg premise is established here from polynomial differentiation.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-heisenberg-commutator"),
                DeclarationHandle.Create(Prefix + "mode_heisenberg"),
                H("Every pair of integer modes has the Heisenberg commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all integer m and n, mode m times mode n "
                    + "minus the reverse product is m times the identity when m+n=0, "
                    + "and zero otherwise. The mixed sign case differentiates a variable "
                    + "multiplier; the two same sign cases commute."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-sugawara-current-commutator"),
                DeclarationHandle.Create(Prefix + "L_mode_commutator"),
                H("The Sugawara operator acts on every mode with weight one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all integer m and r, L m times mode r "
                    + "minus the reverse product is minus r times mode (m+r). "
                    + "Commuting through the pointwise finite sum leaves two singleton "
                    + "contributions. This result does not assert the L-L commutator or "
                    + "its central term."))),
                DescribeRole.Theorem))));
}
