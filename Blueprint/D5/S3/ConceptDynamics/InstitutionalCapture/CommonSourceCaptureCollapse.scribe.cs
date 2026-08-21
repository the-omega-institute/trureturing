using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class CommonSourceCaptureCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common source channel reduces the all-branch capture minimum to one.",
        H("Common-Source Capture Collapse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-source-capture-number-eq-one"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse."
                        + "common_source_capture_number_eq_one"),
                H("A common source collapses the capture number"),
                StatementSource.FromAuthor(CollapseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Source channels and branch outputs are concept readouts from the same "
                            + "state carrier. A controlled set compromises a branch only when one "
                            + "of its members determines that branch output by factorization.")),
                    Paragraph(Text(
                        "The capture number minimizes the cardinality of finite source sets that "
                            + "compromise every branch. Nonemptiness of the branch carrier rules "
                            + "out capture by the empty source set.")),
                    Paragraph(Text(
                        "The common source supplies a capturing singleton, while any zero-cardinal "
                            + "candidate would be empty and could not compromise an existing branch."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula CollapseFormula()
    {
        Formula sourceType = F.Id("Source");
        Formula stateType = F.Id("State");
        Formula signalType = F.Id("Signal");
        Formula branchType = F.Id("Branch");
        Formula resultType = F.Id("Result");
        Formula channel = F.Id("channel");
        Formula output = F.Id("output");
        Formula source = F.Id("s");
        Formula branch = F.Id("i");
        Formula channelAtSource = Apply(channel, source);
        Formula outputAtBranch = Apply(output, branch);
        Formula factorization = Apply(
            Seq(Operatorname, Grp(F.Id("FactorsThrough"))),
            outputAtBranch, channelAtSource);
        Formula commonSource = Seq(
            Forall, Sp, branch, Colon, Sp, branchType, Comma, Sp, factorization);
        Formula capture = Apply(
            Seq(Operatorname, Grp(F.Id("captureNumber"))), channel, output);
        Formula types = Seq(
            sourceType, Comma, Sp, stateType, Comma, Sp, signalType, Comma, Sp,
            branchType, Comma, Sp, resultType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")));
        Formula channelType = Arrow(sourceType, Arrow(stateType, signalType));
        Formula outputType = Arrow(branchType, Arrow(stateType, resultType));

        return Disp(Seq(
            Forall, Sp, types, Comma, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("Nonempty"))), branchType),
            Sp, Rightarrow, Esc,
            Forall, Sp, channel, Colon, Sp, channelType, Comma, Sp,
            output, Colon, Sp, outputType, Comma, Sp,
            source, Colon, Sp, sourceType, Comma, Sp,
            Open, commonSource, Close, Sp, Rightarrow, Esc,
            capture, Sp, Eq, Sp, Num(1), Dot));
    }
}
