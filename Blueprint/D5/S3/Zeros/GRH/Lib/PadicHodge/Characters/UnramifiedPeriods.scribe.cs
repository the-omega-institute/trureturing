using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Characters;

internal sealed class UnramifiedPeriodsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unramified Periods", H("Unramified Periods"),
        Blocks(
            Paragraph(Text("Algebra lemma: killing polynomials in all positive degrees give one in degree zero. Finite type, weights, killing polynomials pass to retracts and along open embeddings. Twisting by a character keeps goodness, shifts weights, rescales killing polynomials. Potentially unramified characters are potentially crystalline, with jumps and Frobenius; Lang for GL_1.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods.isPotCrys_of_unramified_char"),
                H("isPotCrys_of_unramified_char"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j be an open embedding, ν: Γ → Q̄_p^× a continuous character trivial on inertia near 1, acting by scalars on a commutative Q̄_p-algebra T. Then T is potentially crystalline, has the jumps of the trivial action, and X − ν(s) kills (s, k) for Weil pairs (j(s), k).")))))));
}
