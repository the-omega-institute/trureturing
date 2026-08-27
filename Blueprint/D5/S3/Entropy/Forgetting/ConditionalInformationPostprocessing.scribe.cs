using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class ConditionalInformationPostprocessingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Forgetting/ConditionalInformationPostprocessing."
            + "conditional_mutual_information_postprocessing_le";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic postprocessing cannot increase finite conditional mutual information.",
        H("Conditional Information Postprocessing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-mutual-information-postprocessing"),
                DeclarationHandle.Create(Declaration),
                H("Postprocessing lowers conditional mutual information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a finite joint probability law of an environment E, a "
                            + "commitment C, and a future record B.")),
                    Paragraph(Text(
                        "A deterministic map f from B to B prime constructs the coarse law by "
                            + "pushing p forward along the map that preserves E and C and applies "
                            + "f only to B.")),
                    Paragraph(Text(
                        "The mutual-information chain rule and finite Markov data processing "
                            + "show that the conditional information between C and the coarse "
                            + "record given E cannot exceed that of the original record."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula commitment = F.Id("C");
        Formula record = F.Id("B");
        Formula coarseRecord = Seq(record, Apos);
        Formula environment = F.Id("E");
        Formula law = F.Id("p");
        Formula postprocess = F.Id("f");
        Formula point = F.Id("x");
        Formula e = F.Id("e");
        Formula c = F.Id("c");
        Formula b = F.Id("b");
        Formula sourceCarrier = Seq(
            environment, Sp, Times, Sp, Open,
            commitment, Sp, Times, Sp, record, Close);
        Formula targetCarrier = Seq(
            environment, Sp, Times, Sp, Open,
            commitment, Sp, Times, Sp, coarseRecord, Close);
        Formula sourcePoint = Pair(e, Pair(c, b));
        Formula targetPoint = Pair(e, Pair(c, Apply(postprocess, b)));
        Formula processingMap = Seq(
            Open, sourcePoint, Sp, Mapsto, Sp, targetPoint, Close);
        Formula processedLaw = Call("pushforward", processingMap, law);
        Formula probabilityLaw = Seq(
            Open, Forall, Sp, Typed(point, sourceCarrier), Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(law, point), Close, Sp, Land, Sp,
            Sum, Underscore, Grp(point, Sp, InMacro, Sp, sourceCarrier), Sp,
            Apply(law, point), Sp, Eq, Sp, D(1));
        Formula finiteCarriers = Seq(
            Call("Fintype", commitment), Sp, Land, Sp,
            Call("Fintype", record), Sp, Land, Sp,
            Call("Fintype", coarseRecord), Sp, Land, Sp,
            Call("Fintype", environment));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(commitment, type), Comma, Sp,
            Typed(record, type), Comma, Sp,
            Typed(coarseRecord, type), Comma, Sp,
            Typed(environment, type), Comma,
            RowBreak, Grp(),
            finiteCarriers, Comma,
            RowBreak, Grp(),
            Typed(law, Arrow(sourceCarrier, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp,
            Typed(postprocess, Arrow(record, coarseRecord)), Comma,
            RowBreak, Grp(),
            probabilityLaw, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("conditionalMutualInformation", processedLaw), Sp, Leq, Sp,
            Call("conditionalMutualInformation", law), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
