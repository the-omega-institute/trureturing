using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound for three letters of each kind",
        H("The refined BMV lower bound for three letters of each kind"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvlowerbound-l33"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVLowerBound.L33"),
                H("The refined BMV lower bound for three letters of each kind"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
                Blocks(Paragraph(Text(
                    "The inequality holds for every pair of complex Hermitian four-by-four matrices. A trace-power comparison and the Lie–Trotter limit connect the cubic moment bound to the exponential trace."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-33-dimension-four"),
                    ResolutionKind.Proved)))));
}
