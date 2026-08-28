using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class IrrationalSlopeFaithfulnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness."
            + "irrational_slope_observer_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An irrational linear slope faithfully encodes every integer pair as one real value.",
        H("Irrational Slope Faithfulness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("irrational-slope-observer-is-injective"),
                DeclarationHandle.Create(Declaration),
                H("The irrational-slope observer is injective"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of two readings makes the slope times the difference of "
                            + "the first coordinates an integer. If that difference were "
                            + "nonzero, irrationality would be preserved under integer "
                            + "scaling, contradicting the integer value. Both coordinates "
                            + "therefore agree."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alpha = F.Id("alpha");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula pairType = Seq(integers, Sp, Times, Sp, integers);
        Formula observer = Seq(
            Open, Open, m, Comma, Sp, n, Close, Colon, Sp, pairType,
            Sp, Mapsto, Sp, alpha, Sp, m, Sp, Plus, Sp, n, Close);

        return Disp(Seq(
            Forall, Sp, alpha, Colon, Sp, reals, Comma, Sp,
            Call("Irrational", alpha), Sp, Rightarrow, Sp,
            Call("Injective", observer), Dot));
    }
}
