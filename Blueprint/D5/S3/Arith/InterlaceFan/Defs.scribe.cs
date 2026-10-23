using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interlace functionals and rational faces of their fan.",
        H("Interlace fan definitions"), Blocks(
            Paragraph(Text("For darga n, a real coordinate vector has entries indexed from one through floor(n/2). Certificate indices run from zero through floor(n/2). Rational points have rational coordinates. The order class for a divisor d consists of the indices j with n/gcd(n,j)=d.")),
            Describe.Lean(DescribeId.Create("interlace-functional-definition"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Defs.I"),
                H("Interlace functionals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/mandel2019dragging")),
                Blocks(Paragraph(Text("The j-th interlace functional is minus the sum of the sigma coordinates multiplied by cos(2 pi j k/n), with coordinate k ranging from one through floor(n/2). This is equation (12) in section 5.2 of the cited article."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interlace-number-definition"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Defs.interlaceNumber"),
                H("The interlace number"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/mandel2019dragging")),
                Blocks(Paragraph(Text("The interlace number is the maximum of the functionals over indices zero through floor(n/2), as in the Interlace Formula, Theorem 4.2 of the cited article."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interlace-face-definition"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Defs.face"),
                H("Closed certificate faces"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/mandel2019dragging")),
                Blocks(Paragraph(Text("The closed face associated with S consists of all vectors for which every index in S attains the maximum. This is the face convention of section 5.2, Proposition 5.5 and equation (15), in the cited article."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interlace-rational-classification-claim"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Defs.claim"),
                H("The rational-face classification proposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/mandel2019dragging")),
                Blocks(Paragraph(Text("For darga at least two, a nonempty certificate set admits a nonzero rational point precisely when it misses an order class; the maximal such certificate sets are the complements of individual order classes. At a nonzero rational point of the corresponding face, every omitted index has strictly smaller functional value and the interlace number is rational. This is the classification proposition answering section 10, Problem 3 of the cited article."))),
                DescribeRole.Definition))));
}
