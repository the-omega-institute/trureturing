using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformCircuitResidueFormsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting simultaneous exterior equations.",
        H("Uniform Circuit Residue Forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-horizontal-iff"),
                DeclarationHandle.Create(Module + ".closed_horizontal_iff"),
                H("Splitting simultaneous exterior equations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a covector a, a pivot x with a(x) = 1, and an insertion vector y, a form f is "
                    + "annihilated by covector multiplication and by insertion of y exactly when it is the "
                    + "covector product of a form g. The form g must vanish on insertion of either x or y and "
                    + "be killed by the scalar a(y). Insertion of x into f recovers g."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("basis-covector-wedge-apply"),
                DeclarationHandle.Create(Module + ".basis_covectorWedge_apply"),
                H("The signed deletion coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the covector product on an increasing basis tuple sums over its possible "
                    + "deletions, with each term multiplied by the deletion sign and the covector on the "
                    + "deleted vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("curry-left-weighted-basis"),
                DeclarationHandle.Create(Module + ".curryLeft_weighted_basis"),
                H("The weighted insertion coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Inserting a sum of basis vectors with natural number weights gives the signed sum of "
                    + "the enlarged subset coordinates, with each term multiplied by its weight. Coefficients "
                    + "outside the degree of the form are taken to be zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("curry-left-smul-basis-eq-zero-iff"),
                DeclarationHandle.Create(Module + ".curryLeft_smul_basis_eq_zero_iff"),
                H("Insertion of a single basis vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Inserting a scalar multiple of the specified basis vector annihilates a form exactly "
                    + "when that scalar kills every coefficient whose indexing subset contains the specified "
                    + "vector."))),
                DescribeRole.Theorem))));
}
