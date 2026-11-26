using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class TateTwistStepsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tate Twist Steps", H("Tate Twist Steps"),
        Blocks(
            Paragraph(Text("Cocycles in a Tate twist cost only local loss and odd classes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps.hasTriangleCost_tateTwist"),
                H("hasTriangleCost_tateTwist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume IsPrimeTriangle. Let Z be a module of cocycles of O(−e)/ℓ^ν unramified off ℓ, the w_j, w̄_j, whose coboundaries are killed by cyc(γ)^{−e} − 1. If b bounds its local loss at ℓ plus length shaOdd, HasTriangleCost holds with ℓ^h, b.")))))));
}
