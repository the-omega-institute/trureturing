using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class PolynomialBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Numerical polynomial envelopes.",
        H("Numerical polynomial envelopes"),
        Blocks(
            Paragraph(Text("PolynomialBound is only a numerical upper-envelope relation. Sums, products, fixed powers and compositions preserve that relation. These statements do not assign runtime to arbitrary functions; they bound algorithms whose counted executions are separately proved.")),
            Describe.Lean(
                DescribeId.Create("supplied-polynomialbound"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/PolynomialBound.comp"),
                H("PolynomialBound.comp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Clock"))]));
}
