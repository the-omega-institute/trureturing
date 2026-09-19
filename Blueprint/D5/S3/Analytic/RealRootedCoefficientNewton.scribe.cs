using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class RealRootedCoefficientNewtonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef CrownAudit =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real splitting gives strong coefficient Newton inequalities.",
        H("Strong Newton inequalities for real split polynomials"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("split-polynomial-coefficient-newton"),
                DeclarationHandle.Create("D5/S3/Analytic/RealRootedCoefficientNewton.split_polynomial_coefficient_newton"),
                H("Strong Newton inequality at every coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CrownAudit),
                Blocks(
                    Paragraph(Text("For every real polynomial p that splits over the reals and every natural k, (k+1) times the square of coefficient k+1 is at least (k+2) times the product of coefficients k and k+2. No nonnegativity, simplicity of roots, nonzero polynomial or degree bound is assumed. This is the strong unnormalized coefficient form of the classical Newton inequalities; it is not a claim of a new classical inequality.")),
                    Paragraph(Text("Rolle's root-count theorem with multiplicities proves that derivatives of split real polynomials split. Induction on products of real linear and constant factors proves Laguerre positivity at every real point. Evaluating this at zero and inducting on derivatives proves the coefficient inequality with the factorial factors. Applied to the auxiliary scalar polynomial, this gives the Newton inequalities used in the crown log-concavity theorem. The coefficient inequality omits the extra finite-degree factor of the degree-sharp normalized Newton inequalities."))),
                DescribeRole.Theorem))));
}
