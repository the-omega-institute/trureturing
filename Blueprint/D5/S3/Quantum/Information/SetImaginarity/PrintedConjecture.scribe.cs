using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.SetImaginarity;

internal sealed class PrintedConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/guopanwangdu2026setimaginarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three distinct diagonal qubit states refute the biconditional printed as Conjecture 1.",
        H("The printed set imaginarity conjecture"),
        Blocks(
            Definition("common-real-basis", "CommonRealBasis", "One common real basis",
                "For a family indexed by Fin n of complex square matrices on a finite decidable "
                    + "index type, there exists a single unitary U such that every entry of "
                    + "U times the j-th matrix times the adjoint of U has imaginary part zero, "
                    + "for every j and every pair of row and column indices."),
            Definition("trace-word", "traceWord", "Trace of an ordered word",
                "For a family indexed by Fin n and a word w from Fin k to Fin n, take the "
                    + "ordinary complex trace of the product of the states selected by w, "
                    + "in increasing position order. The empty product is the identity. "
                    + "Word positions may select the same state."),
            Definition("printed-claim", "claim", "Conjecture 1 as printed",
                "For all natural d at least two and n at least three, take an injective family of "
                    + "n positive semidefinite complex d by d matrices of trace one. The asserted "
                    + "biconditional equates existence of a common real basis with existence of "
                    + "an ordered word whose trace has nonzero imaginary part, with natural "
                    + "length k between three and the natural quotient d(d+1)/2 inclusive."),
            Describe.Lean(
                DescribeId.Create("printed-refutation"), DeclarationHandle.Create(Prefix + "result"),
                H("Diagonal qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Use the diagonal states with diagonal entries (3/4, 1/4), (1/4, 3/4) "
                        + "and (1/2, 1/2). Their first entries distinguish them, and their "
                        + "diagonals are positive and sum to one. The identity is a common "
                        + "unitary. The inclusion from real matrices to complex matrices "
                        + "preserves ordered products and trace, so every trace word is real. "
                        + "The window at dimension two has length three, and every word "
                        + "in that window therefore has zero imaginary trace."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
