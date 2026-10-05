using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiniteWindowTableCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four independent radii, both seams, both center round trips, finite-group equivariance and finite failure witnesses are lifted between legal finite words and actual histories.",
        H("Finite arbitrary-table criterion"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-global-window-iff"),
                DeclarationHandle.Create(Prefix + "original23_1_finite_global_iff"),
                H("Finite tests are exactly the actual-history tests"),
                StatementSource.FromAuthor(Disp(Call("Iff", Call("FiniteCriterion", F.Id("tests")), Call("GlobalCriterion", F.Id("tests"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The table pair keeps arbitrary f and g at lengths p+q+1 and r+s+1. The common round-trip length is p+q+r+s+1 and the zero-based center is p+r. Essentiality and the prescribed-word realizer make every finite failure visible in an actual history."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-failure-witness"),
                DeclarationHandle.Create(Prefix + "rejected_candidate_has_finite_witness"),
                H("Every rejected candidate has a finite witness"),
                StatementSource.FromAuthor(Disp(Call("Nonempty", Call("FailureWitness", F.Id("pair"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rejected candidate is witnessed by one seam, round-trip, or equivariance window. Fixed radii leave finite domains, so exhaustive candidate checking terminates without asserting a graph-only uniform window bound."))),
                DescribeRole.Theorem))));
}
