using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class SymmetricGainAllocationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Aggregation/SymmetricGainAllocation.symmetric_gain_allocation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal gains above a feasible disagreement point uniquely split the residual resource.",
        H("Symmetric Gain Allocation"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetric-gain-allocation"),
            DeclarationHandle.Create(Declaration),
            H("Equal gains uniquely determine the allocation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The disagreement coordinates are arbitrary real anchors whose sum is at "
                        + "most one. The public statement gives the unique efficient pair with "
                        + "equal gains above those anchors.")),
                Paragraph(Text(
                    "Both allocation coordinates and both gains are displayed explicitly. "
                        + "Feasibility makes the common half-residual gain nonnegative, so the "
                        + "split is relative to the disagreement point rather than an absolute "
                        + "midpoint.")),
                Paragraph(Text(
                    "Ring normalization establishes the equalities, and real linear arithmetic "
                        + "uses the feasibility premise for nonnegativity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula d = F.Id("d");
        Formula d1 = new Formula.Subscript(d, D(1));
        Formula d2 = new Formula.Subscript(d, D(2));
        Formula x = F.Id("x");
        Formula x1 = new Formula.Subscript(x, D(1));
        Formula x2 = new Formula.Subscript(x, D(2));
        Formula pair = Call("Prod", real, real);
        Formula residual = Seq(D(1), Sp, Minus, Sp, d1, Sp, Minus, Sp, d2);
        Formula halfResidual = Seq(Frac, Grp(residual), Grp(D(2)));
        Formula firstValue = Seq(d1, Sp, Plus, Sp, halfResidual);
        Formula secondValue = Seq(d2, Sp, Plus, Sp, halfResidual);
        Formula properties = Seq(
            x1, Sp, Plus, Sp, x2, Sp, Eq, Sp, D(1), Sp, Land, Sp, RowBreak, Grp(),
            x1, Sp, Minus, Sp, d1, Sp, Eq, Sp,
                x2, Sp, Minus, Sp, d2, Sp, Land, Sp, RowBreak, Grp(),
            x1, Sp, Eq, Sp, firstValue, Sp, Land, Sp, RowBreak, Grp(),
            x2, Sp, Eq, Sp, secondValue, Sp, Land, Sp, RowBreak, Grp(),
            x1, Sp, Minus, Sp, d1, Sp, Eq, Sp,
                halfResidual, Sp, Land, Sp, RowBreak, Grp(),
            x2, Sp, Minus, Sp, d2, Sp, Eq, Sp,
                halfResidual, Sp, Land, Sp, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, halfResidual);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d1, Comma, Sp, d2, Colon, Sp, real, Comma, RowBreak, Grp(),
            d1, Sp, Plus, Sp, d2, Sp, Leq, Sp, D(1), Sp,
                Rightarrow, Sp, RowBreak, Grp(),
            Exists, Bang, Sp, x, Colon, Sp, pair, Comma, RowBreak, Grp(),
            properties, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
