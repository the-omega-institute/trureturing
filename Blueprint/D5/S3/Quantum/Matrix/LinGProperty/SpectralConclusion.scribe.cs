using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class SpectralConclusionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized geometric-mean comparison.",
        H("The normalized geometric-mean comparison"), Blocks(
            Describe.Lean(DescribeId.Create("lin-spectralconclusion-0"),
                DeclarationHandle.Create(Owner + "normalized_conclusion"),
                H("The normalized geometric-mean comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("Assume both positive diagonal blocks have trace one and the trace-corrected arithmetic singular-value estimate. Write t=|trace X|. The difference-square estimate bounds the geometric mean below by H-(1-t squared)/(4c) I, where H=cI+(A+B)/2. The scalar perturbation estimate bounds the augmented cross block by the selected eigenvalue of H minus (c-1/2)(1-t). For c at least one and t between zero and one, the latter deficit is at least the former correction."))),
                DescribeRole.Theorem))));
}
