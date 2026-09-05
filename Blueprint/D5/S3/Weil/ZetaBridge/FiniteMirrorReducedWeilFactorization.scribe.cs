using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FiniteMirrorReducedWeilFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/FiniteMirrorReducedWeilFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite convolution-square zero sums factor through the reflection-reduced observable space with analytic multiplicity retained as a positive weight.",
        H("Finite Mirror-Reduced Weil Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truncated-zero-sum-reduced-mirror-factorization"),
                DeclarationHandle.Create(
                    Prefix + "truncatedZeroSum_convolutionSquare_eq_reducedMirrorForm"),
                H("The actual finite convolution-square zero sum is a reduced mirror form"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "truncatedZeroSum Z (convolutionSquare g) T equals the finite multiplicity-weighted mirror form of the reduced evaluation vector"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One scalar coordinate is retained per distinct zero. Functional-equation reflection-evenness is stored as a subtype condition, while analytic multiplicity remains in the quadratic weight and is not counted a second time through duplicated coordinates.")),
                    Paragraph(Text(
                        "The proof uses the frozen complex convolution-square factorization and the stored same-height mirror relation on spectral parameters, then rewrites the finite symmetric cutoff as a subtype sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-off-line-orbit-block-factorization"),
                DeclarationHandle.Create(
                    Prefix + "finite_offLine_orbit_block_factorization"),
                H("Finite orbit blocks split into positive even energy minus positive odd energy"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "finiteOrbitBlockRealValue equals finiteOrbitEvenEnergy minus finiteOrbitOddEnergy"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem sums the established one-orbit parity decomposition over an arbitrary finite family. Both aggregate channel energies remain nonnegative. Orbit disjointness is required only when identifying the block sum with a union of zero indices, not for the algebraic decomposition."))),
                DescribeRole.Theorem)),
        []));
}
