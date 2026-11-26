using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class OrderedSlaterPurityDropEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality in the column-basis lower bound for a strict Slater purity drop.",
        H("Equality in the purity drop of an ordered Slater marginal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-marginal-purity-drop-equality"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality.orderedMarginal_purity_drop_eq_iff"),
                H("Equality for a given column basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Balance one biased retained pair and keep every other endpoint probability. " +
                    "Under strict purity decrease, restrict the alternation matrix to the active " +
                    "discarded pairs. Choose a basis of the columns on the selected row and the " +
                    "other balanced retained rows. Equality in the pivot-column bound holds " +
                    "exactly when the unit row for every nonbalanced basis column and the " +
                    "restricted row for every other nondeterministic biased retained pair differ " +
                    "from the selected row by an element of the span of the other balanced rows. " +
                    "The exact Gram-square trace difference is a weighted sum on the feasible " +
                    "binary fiber. Each free assignment has strictly positive mass, so any strict " +
                    "increase in a factor yields strict excess over the bound."))),
                DescribeRole.Theorem))));
}
