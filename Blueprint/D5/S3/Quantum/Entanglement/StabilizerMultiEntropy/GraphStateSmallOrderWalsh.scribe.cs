using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateSmallOrderWalshDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even-parity hit masses impose a quantitative signed inequality and an exact test for negative type.",
        H("Signed parity separates Walsh hit laws and generators"),
        Blocks(Describe.Lean(DescribeId.Create("generator-gap"),
            DeclarationHandle.Create(Owner + "generator_gap"),
            H("A negative generator rate follows from a finite crossing cancellation"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized")),
            Blocks(
                Paragraph(Text("Invert the negative cut-rank function on the finite vertex-mask group. When the class and singleton cuts have rank one and every straddling pair cut has rank two, odd total labels have zero weight. The signed mass of odd class parity is one half, but every crossing pair has zero signed mass.")),
                Paragraph(Text("On every even label, that parity indicator is bounded by the number of pairs crossing the class. The two mass values therefore force at least one negative rate on an even label meeting both sides. This conclusion uses exact finite character inversion, not a derivative or small-time approximation.")),
                Paragraph(Text("This helper module also proves that a translation kernel is conditionally negative definite exactly when its nontrivial inverse negative Fourier coefficients are nonnegative. The proof diagonalizes the full finite quadratic form into character squares."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        return Disp(new Formula.Relation(F.Id("gamma"), FormulaRelationOperator.LessThan, Num(0)));
    }
}
