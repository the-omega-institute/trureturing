using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class FockTensorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Tensor", H("Fock Tensor"),
        Blocks(
            Paragraph(Text("L1 Fock space, polynomial vectors, derivative of the Heisenberg action on them. Transport of the coefficient model along linear or conjugate-linear isomorphisms. Tensor products of Fock vectors and block diagonal action over places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/FockTensor.measurePreserving_equiv"),
                H("measurePreserving_equiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let e, e' be vacua (Heisenberg.IsVacuum) for Haar measures μ on W and μ' on W'. An isomorphism of topological groups φ : W' → W with e ∘ φ = e' carries μ' to μ.")))))));
}
