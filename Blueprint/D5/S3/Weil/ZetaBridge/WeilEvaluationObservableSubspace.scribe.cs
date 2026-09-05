using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilEvaluationObservableSubspaceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/WeilEvaluationObservableSubspace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar even Weil evaluation is constant on analytic-multiplicity fibers and invariant under functional-equation reflection, producing explicit finite rank obstructions.",
        H("Weil Evaluation Observable Subspace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-weil-evaluation-observable-subspace"),
                DeclarationHandle.Create(
                    Prefix + "finite_weil_evaluation_observable_subspace_spec"),
                H("Finite scalar Weil evaluations obey both observable-range constraints"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "evaluation vectors are multiplicity-fiber constant and reflection even"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite coordinate evaluation repeats one Fourier-Laplace value over every analytic-multiplicity copy. The finite index evaluation is unchanged by functional-equation reflection because bundled Weil tests are even.")),
                    Paragraph(Text(
                        "The module constructs explicit target vectors proving non-surjectivity whenever a multiplicity fiber has at least two copies or the window contains a moved reflection pair. These are genuine observer-rank obstructions, not dimension-counting assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("multiplicity-copy-rank-obstruction"),
                DeclarationHandle.Create(
                    Prefix + "finiteWeilCoordinateEvaluation_not_surjective_of_two_copies"),
                H("Multiplicity copies obstruct ambient surjectivity"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "multiplicity at least two implies scalar coordinate evaluation is not surjective"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A scalar test cannot assign different values to two copies of the same analytic zero. The proof supplies an explicit ambient target vector separating the two copies and derives a contradiction from fiber constancy."))),
                DescribeRole.Theorem)),
        []));
}
