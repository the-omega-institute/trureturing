using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class EightTriangleEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/EightTriangleEnvelope.high_upper_sq";

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
                "With a=5/4 and c=4/3, the lower-face cosines are "
                + "73/100, 8 sqrt(6)/27, and 293/400; the upper-face cosines are "
                + "121/175, 13 sqrt(41)/123, and 473/700. Their squared margins "
                + "are respectively on the correct sides of 1/2, so eight occurrences "
                + "give strict pi/4 angle budgets. A high edge has upper cosine at most "
                + "53/59, which is below cos(pi/7), hence degree at least fourteen gives "
                + "strictly more than 2 pi.")),
            Paragraph(Text(
                "The formal Lean file checks these exact arithmetic margins. The "
                + "six-variable formula, monotonicity, topology of face pairings and "
                + "the co-volume minimum are cited ordinary mathematics in the theory "
                + "document; this Scribe statement does not silently promote them "
                + "to formal premises.")),
            Describe.Lean(
                DescribeId.Create("hyperideal-eight-triangle-envelope"),
                DeclarationHandle.Create(Declaration),
                H("High-edge endpoint margin"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                Blocks(Paragraph(Text(
                    "The conclusion is an exact real inequality, independent of any "
                    + "finite enumeration or numerical sampling."))),
                DescribeRole.Theorem))));
    
    private static Formula Statement() =>
        new Formula.Relation(
            F.Div(F.Pow(F.D(23), F.D(2)), F.Pow(F.D(25), F.D(2))),
            FormulaRelationOperator.LessThan,
            F.Div(F.Add(F.D(2), F.Call("Real.sqrt", F.D(2))), F.D(4)));
}
