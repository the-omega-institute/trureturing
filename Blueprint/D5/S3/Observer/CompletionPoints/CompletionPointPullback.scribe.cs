using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CompletionPoints;

internal sealed class CompletionPointPullbackDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/CompletionPoints/CompletionPointPullback.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completion points pull back exactly along a change of state representation.",
        H("Completion Point Pullback"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-completion-pulls-back-by-composition"),
                DeclarationHandle.Create(Prefix + "zero_at_pullback"),
                H("Pointwise completion pulls back by composition"),
                StatementSource.FromAuthor(PointStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Map a source state into the target state space and evaluate the target "
                            + "defect there.")),
                    Paragraph(Text(
                        "Zero defect for the composite at the source is definitionally equivalent "
                            + "to zero defect at the mapped target state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-pulled-back-zero-set-is-a-preimage"),
                DeclarationHandle.Create(Prefix + "zero_set_pullback"),
                H("The pulled-back zero set is a preimage"),
                StatementSource.FromAuthor(SetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Collect the source states where the composite defect vanishes.")),
                    Paragraph(Text(
                        "This set is exactly the preimage under the state map of the target "
                            + "defect's zero set."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion, bool includeSource)
    {
        Formula sourceBinder = includeSource
            ? Seq(F.Id("x"), Colon, Sp, F.Id("S"), Comma, Sp)
            : Seq();
        return Disp(Seq(
            Forall, Sp, F.Id("mapState"), Colon, Sp,
            Arrow(F.Id("S"), F.Id("T")), Comma, Sp,
            F.Id("defect"), Colon, Sp, Arrow(F.Id("T"), F.Id("D")), Comma, Sp,
            F.Id("zero"), Colon, Sp, F.Id("D"), Comma, Sp,
            sourceBinder, conclusion, Dot));
    }

    private static Formula PointStatement()
    {
        Formula composite = Seq(F.Id("defect"), Sp, Circ, Sp, F.Id("mapState"));
        Formula left = Call("ZeroAt", composite, F.Id("zero"), F.Id("x"));
        Formula right = Call("ZeroAt", F.Id("defect"), F.Id("zero"),
            Call("mapState", F.Id("x")));
        return PrefixFormula(Seq(left, Sp, Iff, Sp, right), true);
    }

    private static Formula SetStatement()
    {
        Formula composite = Seq(F.Id("defect"), Sp, Circ, Sp, F.Id("mapState"));
        Formula left = Call("zeroSet", composite, F.Id("zero"));
        Formula right = Call("preimage", F.Id("mapState"),
            Call("zeroSet", F.Id("defect"), F.Id("zero")));
        return PrefixFormula(Seq(left, Sp, Eq, Sp, right), false);
    }
}
