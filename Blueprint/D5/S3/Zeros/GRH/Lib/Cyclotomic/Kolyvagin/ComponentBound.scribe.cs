using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cyclotomic.Kolyvagin;

internal sealed class ComponentBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Component Bound", H("Component Bound"),
        Blocks(
            Paragraph(Text("Kolyvagin derivative cocycles of Gauss sums: ramification and the Frobenius-to-inertia relation. Artin reciprocity and Kummer duality relations for twisted cocycles over cyclotomic fields. Stickelberger annihilation of odd twisted classes; Kolyvagin-Rubin bound on detecting elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound.exists_detecting_points_component"),
                H("exists_detecting_points_component"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Kolyvagin–Rubin bound. Under the hypotheses of nsmul_component_eq_zero (these already make O local and each O/lⁿ finite), with X ≠ 0 and l > N + e + 3, there are v_l(X) + 1 Galois elements such that a cocycle in component vanishing at all of them is zero.")))))));
}
