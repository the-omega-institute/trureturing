using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.Hadamard;

internal sealed class BanicaCycleForestIncidenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integration of edge values on a cyclic group with a vertex removed.",
        H("Incidence on a cut circle"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-forest-edges"),
                DeclarationHandle.Create(Prefix + "Edges"),
                H("Induced directed edges"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An edge starts at a vertex in S and ends at its translate by a, also in S."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cycle-forest-incidence-surjective"),
                DeclarationHandle.Create(Prefix + "cycle_incidence_surjective"),
                H("Every edge assignment integrates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any positive modulus, a proper vertex subset, a unit step, and an abelian group of edge values, the vertex-difference map is surjective.")),
                    Paragraph(Text("Choose a missing vertex o. The coordinate of x is the least nonnegative residue of (x-o)/a. Along an induced edge that coordinate increases by exactly one, because its endpoint cannot be o. The negative cumulative sum of extended edge values therefore has the prescribed difference at every induced edge. No assumption about an existing inverse is used."))),
                DescribeRole.Theorem))));
}
