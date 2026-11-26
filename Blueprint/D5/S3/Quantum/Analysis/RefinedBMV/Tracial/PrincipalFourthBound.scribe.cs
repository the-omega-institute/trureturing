using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class PrincipalFourthBoundDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/PrincipalFourthBound.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Principal minors and the four-copy refined BMV lower bound",
        H("Principal minors and the four-copy refined BMV lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-signed-principal-minors"),
                DeclarationHandle.Create(Module + "diagonal_word_bound_of_signed_minors"),
                H("Ordered-word comparison under principal minor signs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let the first factor be diagonal with nonnegative entries. Suppose every " +
                    "principal minor of order j between one and four of the second factor has " +
                    "sign (-1)^(j+1), allowing zero. The mean of the words with any number of first " +
                    "factors and four second factors dominates their balanced product trace. " +
                    "The scalar kernel depends only on the multiplicities of the spectral labels. " +
                    "The signed minors give nonnegative grouped coefficients of the fourth power trace " +
                    "through the reversed characteristic polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-one-positive-eigenvalue"),
                DeclarationHandle.Create(Module + "diagonal_word_bound_of_posIndex"),
                H("Hermitian second factors with positive index at most one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The same word comparison holds for a Hermitian second factor with at most one " +
                    "positive eigenvalue and nonnegative diagonal in the displayed basis. Principal " +
                    "compression preserves the upper bound on positive inertia. A nonsingular " +
                    "nonempty compression has nonnegative trace and therefore exactly one positive " +
                    "eigenvalue. Singular compressions have zero determinant."))),
                DescribeRole.Theorem))));
}
