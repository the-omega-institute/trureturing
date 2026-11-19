using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitLineTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The twelve-color theorem on every actual line of binary six-space.",
        H("Complete source-to-target graph transport"),
        Blocks(Describe.Lean(DescribeId.Create("actual-six-dimensional-line-chromatic-number"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineTransfer.result"),
            H("The actual induced line graph has chromatic number twelve"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/QuadraticForms/binarysubspace2026complete")),
            Blocks(Paragraph(Text(
                "The exact low-bit coordinate equivalence identifies every nonzero source "
                + "mask with a nonzero vector in Fin6->ZMod2. Dot-zero and distinctness are "
                + "preserved in both directions. The all-dimensional vector/line isomorphism "
                + "then reaches the full induced graph on actual one-dimensional Submodules. "
                + "The root weighted check, every independent-set weight bound, all actual "
                + "color fibers and the unchanged literal twelve classes discharge the source "
                + "theorem used here. This is the separate O2 theorem, not the all-subspace "
                + "fifteen-color theorem and not an n7 upper bound. Publication, rights and "
                + "author-order decisions remain outside this formal delivery."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/BinaryLineGraph"))]));
}
