using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class PartialNameAssignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional laws for a finite random injective naming.",
        H("Guessing an available name after a partial observation"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-remaining-name-hit"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Probability/PartialNameAssignment.uniform_remaining_name_hit"),
            H("A name hits with probability equal to the remaining density"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Choose an injection uniformly from a finite vertex set into a finite name set. "
                    + "Fix an injective naming on a subset of vertices and an available name set "
                    + "disjoint from those fixed names. Condition on agreement with the fixed "
                    + "naming and on every other vertex receiving an available name. Assume a "
                    + "consistent injection exists.")),
                Paragraph(Text(
                    "The conditional law is uniform on consistent injections. For each available "
                    + "name, its mass of being assigned to one of the remaining vertices is the "
                    + "number of remaining vertices divided by the number of available names.")),
                Paragraph(Text(
                    "Restricting a consistent injection to the remaining vertices gives a "
                    + "bijection with injections into the available name set. Swapping two "
                    + "available names exchanges the corresponding evaluation fibers. Each "
                    + "remaining vertex therefore has the same probability of taking the given "
                    + "name. Injectivity makes the hit events for different vertices disjoint."))),
            DescribeRole.Theorem))));
}
