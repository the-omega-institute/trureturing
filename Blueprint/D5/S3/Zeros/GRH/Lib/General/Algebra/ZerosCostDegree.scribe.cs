using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class ZerosCostDegreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeros Cost Degree", H("Zeros Cost Degree"),
        Blocks(
            Paragraph(Text("Schur modules, Weyl lattices, Fischer product, kernel, Gram form, symmetric powers: definitions. High-order vanishing at all points of a complete intersection forces large weighted degree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree.exists_le_cost_of_vanishing"),
                H("exists_le_cost_of_vanishing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Give the variable u the cost 1/κ_u. Take at least ∏κ_u distinct points at which each u^{κ_u} agrees with a polynomial whose monomials cost less than 1. Then every f ≠ 0 vanishing to order d at these points has a monomial of cost at least d.")))))));
}
