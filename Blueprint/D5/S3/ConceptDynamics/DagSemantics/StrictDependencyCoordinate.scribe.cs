using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class StrictDependencyCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strictly increasing dependency coordinate linearizes paths and forbids cycles.",
        H("Strict Dependency Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-coordinate-increases-along-paths"),
                DeclarationHandle.Create(Prefix + "strict_of_transGen"),
                H("Strict coordinates increase along nonempty paths"),
                StatementSource.FromAuthor(PathFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In a preordered rank carrier, assume every dependency edge strictly "
                            + "increases a coordinate. A supplied nonempty dependency path then "
                            + "strictly increases its endpoint ranks.")),
                    Paragraph(Text(
                        "The nonempty TransGen path is an explicit premise; no strict conclusion "
                            + "is claimed for a merely reflexive path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-coordinate-forbids-cycles"),
                DeclarationHandle.Create(Prefix + "acyclic_of_strictCoordinate"),
                H("Strict coordinates forbid directed cycles"),
                StatementSource.FromAuthor(AcyclicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same strict-coordinate hypothesis, no vertex supports a "
                            + "nonempty dependency path back to itself.")),
                    Paragraph(Text(
                        "The conclusion rules out TransGen self-cycles. It does not rule out the "
                            + "reflexive witness present in ReflTransGen."))),
                DescribeRole.Theorem))));

    private static Formula Common(Formula conclusion)
    {
        Formula edge = F.Id("edge");
        Formula coordinate = F.Id("coordinate");

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            coordinate, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("Rank"),
            Comma, RowBreak, Grp(),
            OpenBracket, Call("Preorder", F.Id("Rank")), CloseBracket,
            Comma, RowBreak, Grp(),
            Call("StrictDependencyCoordinate", edge, coordinate), Sp, Rightarrow,
            RowBreak, Grp(), conclusion, Dot));
    }

    private static Formula PathFormula() => Common(Seq(
        Forall, Sp, F.Id("first"), Comma, Sp, F.Id("last"), Colon, Sp, F.Id("V"),
        Comma, Sp,
        Call("TransGen", F.Id("edge"), F.Id("first"), F.Id("last")),
        Sp, Rightarrow, Sp,
        Call("coordinate", F.Id("first")), Sp, Lt, Sp,
        Call("coordinate", F.Id("last"))));

    private static Formula AcyclicFormula() => Common(Seq(
        Forall, Sp, F.Id("vertex"), Colon, Sp, F.Id("V"), Comma, Sp,
        Neg, Sp, Call("TransGen", F.Id("edge"), F.Id("vertex"), F.Id("vertex"))));
}
