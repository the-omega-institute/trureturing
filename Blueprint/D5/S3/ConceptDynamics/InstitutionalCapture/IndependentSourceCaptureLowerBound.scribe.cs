using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class IndependentSourceCaptureLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent irreplaceable branch sources impose a capture lower bound.",
        H("Independent-Source Capture Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-source-capture-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/"
                        + "IndependentSourceCaptureLowerBound."
                        + "independent_source_capture_lower_bound"),
                H("Independent sources force one captured source per branch"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each branch has an assigned source, distinct branches receive distinct "
                            + "sources, and a source determines a branch output exactly when it is "
                            + "that branch's assigned source.")),
                    Paragraph(Text(
                        "Any finite source set that captures every branch must therefore contain "
                            + "the entire range of the assignment: a source witnessing capture of "
                            + "a branch can only be its assigned source.")),
                    Paragraph(Text(
                        "The assigned-source range itself captures every branch, so admissible "
                            + "finite capture sets exist. Its injective cardinality is the number "
                            + "of branches. Inclusion in a minimum capture set then gives the "
                            + "lower bound."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula LowerBoundFormula()
    {
        Formula sourceType = F.Id("Source");
        Formula stateType = F.Id("State");
        Formula signalType = F.Id("Signal");
        Formula branchType = F.Id("Branch");
        Formula resultType = F.Id("Result");
        Formula channel = F.Id("channel");
        Formula output = F.Id("output");
        Formula source = F.Id("source");
        Formula branch = F.Id("branch");
        Formula candidate = F.Id("candidate");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula types = Seq(
            sourceType, Comma, Sp, stateType, Comma, Sp, signalType, Comma, Sp,
            branchType, Comma, Sp, resultType, Colon, Sp, type);
        Formula channelType = Arrow(sourceType, Arrow(stateType, signalType));
        Formula outputType = Arrow(branchType, Arrow(stateType, resultType));
        Formula factorization = Call(
            "FactorsThrough", Apply(output, branch), Apply(channel, candidate));
        Formula exactSource = Seq(
            Forall, Sp, branch, Colon, Sp, branchType, Comma, Sp,
            candidate, Colon, Sp, sourceType, Comma, Sp,
            factorization, Sp, Iff, Sp,
            candidate, Sp, Eq, Sp, Apply(source, branch));
        Formula independence = Seq(
            Call("Injective", source), Sp, Land, Esc, exactSource);
        Formula capture = Call("captureNumber", channel, output);

        return Disp(Seq(
            Forall, Sp, types, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open,
            branchType, Close, CloseBracket, Comma, Esc,
            Forall, Sp, channel, Colon, Sp, channelType, Comma, Sp,
            output, Colon, Sp, outputType, Comma, Sp,
            source, Colon, Sp, Arrow(branchType, sourceType), Comma, Esc,
            Open, independence, Close, Sp, Rightarrow, Esc,
            Call("card", branchType), Sp, Leq, Sp, capture, Dot));
    }
}
