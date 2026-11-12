using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanFiniteRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic periodizer bridge for finite-alphabet lattice configurations.",
        H("KhetanFiniteRecurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("directional-recurrence-uniform-period"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence.directional_recurrence_uniform_period"),
                H("A common period for all recurrent lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A recurrence of order r with nonzero leading coefficient acts at every lattice site. States contain r+1 values from the global finite alphabet. Their deterministic successor gives each line a positive period at most alphabet-size^(r+1); the factorial is one period of the entire configuration. Order zero and zero constant coefficient are included."))),
                DescribeRole.Theorem))));
}
