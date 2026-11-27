using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Analysis;

internal sealed class OstrowskiTausskyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ostrowski Taussky", H("Ostrowski Taussky"),
        Blocks(
            Paragraph(Text("Elementary lower bound n ≤ φ(n)(2 log n + 1) for Euler's totient. Schur polynomials in polynomial coefficients; bialternant formula with the Vandermonde determinant. Tube lemma for a jointly continuous map over a compact set. Strong integral of a family of bounded operators; small calculus helpers. Ostrowski-Taussky determinant inequality; operator norm versus matrix entries.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Analysis/OstrowskiTaussky.ostrowski_taussky"),
                H("ostrowski_taussky"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Ostrowski–Taussky inequality: if H is a positive semidefinite complex n × n matrix and Θ + Θ* − H is positive semidefinite, then |det H| ≤ 2^n |det Θ|.")))))));
}
