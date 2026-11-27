using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class PartitionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partitions", H("Partitions"),
        Blocks(
            Paragraph(Text("Dense subfunctors form a Grothendieck topology; Mayer–Vietoris short exact sequence. Composition of pull-backs; an equivalence can be checked over a dense subfunctor. Idempotent partitions and Zariski-local subfunctors are dense for additive coefficients on comparable rings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Partitions.hasZariskiDescent"),
                H("hasZariskiDescent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F satisfy HasPartitions for ι and let η: ι → κ be injective. If any a, b ∈ κ(A) have an idempotent e ∈ ι(A) with a ∣ η(e)b and b ∣ (1 − η(e))a, then F satisfies Zariski descent HasZariskiDescent for κ.")))))));
}
