using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockVirasoroCentralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/kytola2025virasoro");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual complex polynomial Fock Sugawara operators satisfy the central charge one relation.",
        H("Polynomial Fock Virasoro Central Relation"),
        Blocks(
            Paragraph(Text("The operators are the pointwise finite normal-ordered sums on "
                + "complex polynomials in countably many variables. The proof is a source "
                + "transplant of Kytola's bosonic Sugawara proof, specialized to these "
                + "operators using their support bounds and Heisenberg-current relations.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-virasoro-central-relation"),
                DeclarationHandle.Create(Prefix + "L_commutator"),
                H("Every pair of integer Sugawara modes has the central commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all integers m and n, L m times L n minus the "
                    + "reverse product equals (m-n) times L (m+n), plus (m cubed minus m)/12 "
                    + "times the identity when m+n=0. The central coefficient comes from "
                    + "the two finite integer sign intervals of the normal-ordering boundary. "
                    + "This is a rank-one c=1 operator relation, not a construction of a VOA, "
                    + "Monster modules, c=24, fusion, conformal weights or OPE coefficients."))),
                DescribeRole.Theorem))));
}
