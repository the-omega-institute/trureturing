using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class ActualNestedQIterateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original complete nested residue iterate", H("ActualNestedQIterate"), Blocks(
            Describe.Lean(DescribeId.Create("actual-nested-q-iterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate.actual_nested_q_iterate"), H("actual_nested_q_iterate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The supplied Laurent polynomial P and cutoff K are arbitrary. The universal coefficient equation is the original actual three-field numerator equation for every integer exponent. The first complete-field locality H1, the function H2 over range((K-r).toNat), and H3 over range(vectorFrequencyBound b+1) are independent. All signed lifts, modes, input vectors and algebraic duals are retained. The three exact actual outer-residue/Taylor identifications share one numerator. Their finite collision balance gives the actual nested-Q iterate, including negative total degree and empty support ranges. This helper is consumed by the native first-source current step."))), DescribeRole.Theorem))));
}
