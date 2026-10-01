using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterFanoReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterFanoReconstruction.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/basak2017monstercharactercarry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven-point unique pair incidence forces symmetric-difference complement closure.",
        H("Monster Fano Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monster-fano-block-intersection"),
                DeclarationHandle.Create(Prefix + "block_intersection_le_one"),
                H("Distinct blocks share at most one point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Unique pair incidence alone bounds the intersection of "
                        + "two distinct blocks by one point. Two distinct common points would "
                        + "make both blocks witnesses to the same unique block, a contradiction. "
                        + "No block cardinality, additive closure, labeling, or enumeration is used.")),
                    Paragraph(Text("This is the first formalized incidence premise in the Fano "
                        + "closure argument of PR #10310 section 30.1. It does not construct "
                        + "VOA modules, fusion products, conformal weights, or a CFT."))),
                DescribeRole.Theorem),
            Paragraph(Text("A block system consists of three-element subsets of seven points. "
                + "Every two distinct points lie in exactly one block. No labeling, additive "
                + "presentation, intersection rule, or block count is assumed.")),
            Describe.Lean(
                DescribeId.Create("monster-fano-complement-symmetric-difference"),
                DeclarationHandle.Create(Prefix + "complement_symmDiff_mem"),
                H("Complement of a symmetric difference is a block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Two different blocks cannot share a pair. Disjoint blocks "
                        + "would leave a single outside point, forcing incompatible blocks "
                        + "through cross-pairs. Thus different blocks meet at exactly one point.")),
                    Paragraph(Text("The unique block through the two points outside their union "
                        + "must also contain their common point. It is exactly the complement "
                        + "of their symmetric difference. This is a finite incidence theorem; "
                        + "it does not construct VOA modules, fusion, or conformal spectra."))),
                DescribeRole.Theorem))));
}
