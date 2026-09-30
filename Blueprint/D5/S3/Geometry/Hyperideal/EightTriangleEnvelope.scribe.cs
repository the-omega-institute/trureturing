using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class EightTriangleEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/EightTriangleEnvelope.high_upper_taylor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent degree-eight packets: exact endpoint margins",
        H("A strict CFMP subcase with adjacent low edges"),
        Blocks(
            Paragraph(Text(
                "Global edges have degree eight or at least fourteen. In each tetrahedron, "
                + "the degree-eight local edges form either a three-star, a three-cycle, "
                + "or a four-cycle, and each low edge has exactly two low neighbours. "
                + "The new case is the adjacent three-star/three-cycle packet.")),
            Paragraph(Text(
                "With a=5/4 and c=10/7, the lower-face cosines are "
                + "73/100, 8 sqrt(6)/27, and 293/400; the upper-face cosines are "
                + "709/1003, 11 sqrt(249)/249, and 2753/4012. Their squared margins "
                + "are respectively on the correct sides of 1/2, so eight occurrences "
                + "give strict pi/4 angle budgets. A high edge has upper cosine at most "
                + "53/59, which is below cos(pi/7) by the exact Taylor certificate "
                + "at 22/49, hence degree at least fourteen gives strict budget.")),
            Paragraph(Text(
                "The formal Lean file checks these exact arithmetic margins and the "
                + "Taylor polynomial comparison. The six-variable formula, monotonicity, "
                + "topology of face pairings and the co-volume minimum are cited ordinary "
                + "mathematics in the theory document; this Scribe statement does not "
                + "silently promote them to formal premises.")),
            Describe.Lean(
                DescribeId.Create("hyperideal-eight-triangle-envelope"),
                DeclarationHandle.Create(Declaration),
                H("High-edge Taylor margin"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conclusion is an exact real inequality, independent of any "
                    + "finite enumeration or numerical sampling."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => F.Id("highUpperTaylor");
}
