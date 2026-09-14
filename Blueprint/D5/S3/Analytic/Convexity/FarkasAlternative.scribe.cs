using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class FarkasAlternativeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/dvorak2024duality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite Bartl recursion supplies Farkas alternatives over ordered scalars.",
        H("Finite Farkas Alternatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-bartl-alternative"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/FarkasAlternative.fin_farkas_bartl"),
                H("Finite Bartl alternative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let R be a linearly ordered division ring, V a linearly ordered additive commutative group with an R-module structure whose scalar action is monotone for nonnegative scalars, and W an additive commutative group with an R-module structure. For every natural number n, linear map A from W to Fin n → R, and linear map b from W to V, exactly one of the following alternatives holds.")),
                    Paragraph(Text("There exists a componentwise nonnegative vector x : Fin n → V such that, for every w : W, the sum of A(w,j) acting on x(j) equals b(w); or there exists y : W such that A(y) is componentwise nonnegative and b(y) is strictly negative. The Lean statement expresses exclusivity and exhaustiveness by inequality of the two propositions.")),
                    Paragraph(Text("The recursion either appends a zero coefficient to the shorter representation, or rescales a separating direction and restores the last coefficient after eliminating its coordinate. No commutativity of multiplication in R is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inequality-alternative"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/FarkasAlternative.inequality_farkas_neg"),
                H("Inequality alternative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For arbitrary finite row and column types I and J over a linearly ordered field F, with decidable equality on I, exactly one alternative holds: a nonnegative x satisfies A x ≤ b; or a nonnegative y satisfies −Aᵀ y ≤ 0 and b · y < 0. The coordinate interpretation of the Bartl theorem and the addition of nonnegative slack variables give this interface."))),
                DescribeRole.Theorem))));
}
