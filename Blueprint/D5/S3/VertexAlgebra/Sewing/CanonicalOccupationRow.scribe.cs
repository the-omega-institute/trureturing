using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sewing;

internal sealed class CanonicalOccupationRowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal occupation coordinates and private coefficient estimates consumed by canonical occupation sewing.",
        H("Canonical occupation coordinates and row bounds"),
        Blocks(
            Paragraph(Text("This companion supplies the literal occupation coordinates for CanonicalOccupation.canonical_sewing_summable. Every lattice D, integral charge and signed mode remains arbitrary; occupations have no cutoff.")),
            Node("Occ", "Internal occupations", "All finitely supported natural occupations on Fin D.rank times Nat.", DescribeRole.Definition),
            Node("level", "Oscillator energy", "The existing positive integer oscillator energy, with frequency k+1 at index (i,k).", DescribeRole.Definition),
            Node("b", "Literal monomial state", "The monomial with occupation d and coefficient one in the original oscillator polynomial carrier.", DescribeRole.Definition),
            Node("creationCoordinate", "Creation occupation numerator", "The finite product of (alpha(i)/(k+1)) to the occupation multiplicity, obtained from the original creation exponential.", DescribeRole.Definition),
            Paragraph(Text("The private creation-coefficient proof differentiates the original creation exponential and identifies its exact factorial coordinate. The public LatticeActualProductKernel convolution and raw creator supply the actual creation-and-translation field. Both original normal-product branches, including the charge zero mode, yield a finite word-coefficient recurrence. Induction on the actual descendant word gives the uniform row envelope C(1+level(d))^K L^degree(d). CanonicalOccupation imports the private coefficient, recurrence and row helpers for its complementary column bound and final literal scalar contraction; no separate public estimate theorem is introduced.")),
            Paragraph(Text("The lattice-field and normal-product attributions remain those of the imported Bakalov--Kac, Matsuo--Nagatomo and Carnahan suppliers. Mathlib supplies polynomial derivatives and finite-support estimates. These coordinates and private estimates do not assert an invariant BPZ form, physical unitarity, operator convergence, channel reassociation or complete CFT sewing."))),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("canonical-occupation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
