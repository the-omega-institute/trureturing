using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteLocalizerIndexDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/FiniteLocalizerIndex.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian spectral localizers inherit finite positive, negative, and signed inertia indices with exact sign-pattern invariance.",
        H("Finite Localizer Inertia Index"),
        Blocks(
            Def("negative", "finiteLocalizerNegativeIndex", "Localizer negative index",
                "The repository-standard Hermitian negative inertia count is applied to the finite spectral localizer."),
            Def("positive", "finiteLocalizerPositiveIndex", "Localizer positive index",
                "The repository-standard Hermitian positive inertia count is applied to the finite spectral localizer."),
            Def("signed", "finiteLocalizerSignedIndex", "Signed localizer index",
                "The finite signed index is positive inertia minus negative inertia."),
            Def("pattern", "SameHermitianSignPattern", "Hermitian sign pattern",
                "Two Hermitian matrices have matching negative and positive eigenvalue predicates at every indexed eigenvalue."),
            Thm("negative-pattern", "negIndex_eq_of_same_negative_pattern", "Negative inertia depends only on negative signs",
                "Matching negative eigenvalue predicates give equal negative inertia counts."),
            Thm("positive-pattern", "posIndex_eq_of_same_positive_pattern", "Positive inertia depends only on positive signs",
                "Matching positive eigenvalue predicates give equal positive inertia counts."),
            Thm("signed-pattern", "signedIndex_eq_of_same_sign_pattern", "Signed inertia is sign-pattern invariant",
                "Preserving both positive and negative eigenvalue classifications preserves the signed index."),
            Thm("localizer-pattern", "finiteLocalizerSignedIndex_eq_of_same_sign_pattern", "Localizer index is sign-pattern invariant",
                "Two finite localizers with the same Hermitian spectral sign pattern have the same signed index."),
            Thm("change", "index_change_forces_sign_pattern_change", "Index change forces spectral sign change",
                "Different localizer indices rule out preservation of the complete positive and negative sign pattern.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FinitePointGapLocalizer")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaLinear/PosIndex")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
