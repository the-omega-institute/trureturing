using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class UnrestrictedBinaryQuestionDepthOptimalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Identifiability/UnrestrictedBinaryQuestionDepthOptimality."
            + "unrestricted_binary_question_depth_optimality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted binary questions attain the exact finite repair depth.",
        H("Unrestricted Binary Question Depth"),
        Blocks(Describe.Lean(
            DescribeId.Create("unrestricted-binary-question-depth-optimality"),
            DeclarationHandle.Create(Declaration),
            H("Adaptive identification and exact repair have the same least width"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The canonical protocol assigns fixed-length bit vectors to target values "
                        + "realized within each current-concept fiber and asks their bits "
                        + "sequentially.")),
                Paragraph(Text(
                    "The protocol construction attains the ceiling binary logarithm of worst "
                        + "fiber diversity. The adaptive lower bound and the exact binary-label "
                        + "minimum show that the same width is least for both tasks."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("C");
        Formula targetCarrier = F.Id("Target");
        Formula current = F.Id("c");
        Formula target = F.Id("t");
        Formula depth = F.Id("d");
        Formula width = F.Id("k");
        Formula protocol = F.Id("pi");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula optimum = Call(
            "clog",
            D(2),
            Call("worstFiberDiversity", current, target));
        Formula protocolDepths = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, naturalNumbers, Sp, Mid, Sp,
            Exists, Sp, protocol, Colon, Sp,
            Call("BinaryProtocol", state, depth), Comma, Sp,
            Call("IdentifiesGiven", current, target, protocol), CloseBrace);
        Formula repairWidths = Seq(
            OpenBrace, width, Sp, InMacro, Sp, naturalNumbers, Sp, Mid, Sp,
            Call("BinaryRepairFeasible", current, target, width), CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, coordinate, Comma, Sp, targetCarrier,
                Comma),
            Seq(
                Call("Fintype", state), Sp, Land, Sp,
                Call("Fintype", coordinate), Comma),
            Seq(
                current, Colon, Sp, state, Sp, To, Sp, coordinate, Comma, Sp,
                target, Colon, Sp, state, Sp, To, Sp, targetCarrier, Comma),
            Seq(
                Call("IsLeast", protocolDepths, optimum), Sp, Land),
            Seq(
                Call("IsLeast", repairWidths, optimum), Dot),
        ]));
    }

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
}
