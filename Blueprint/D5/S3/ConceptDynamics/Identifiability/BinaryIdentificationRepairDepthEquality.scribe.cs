using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class BinaryIdentificationRepairDepthEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Identifiability/BinaryIdentificationRepairDepthEquality."
            + "unconstrained_binary_identification_depth_equals_repair_bits";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconstrained binary identification has the same least depth as exact repair width.",
        H("Binary Identification and Repair Depth Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("unconstrained-binary-identification-depth-equals-repair-bits"),
            DeclarationHandle.Create(Declaration),
            H("Least adaptive depth equals least binary repair width"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Worst fiber diversity counts the largest number of target values "
                        + "realized under one current-concept coordinate.")),
                Paragraph(Text(
                    "The public statement exposes both least-element claims. The adaptive "
                        + "membership clause contains an identifying protocol, while the "
                        + "repair membership clause contains a target-determining bit label.")),
                Paragraph(Text(
                    "The frozen construction, adaptive lower bound, and exact repair-cost "
                        + "theorem give the common ceiling binary logarithm."))),
            DescribeRole.Theorem))));

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

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("C");
        Formula targetCarrier = F.Id("Target");
        Formula current = F.Id("c");
        Formula target = F.Id("t");
        Formula adaptiveDepth = F.Id("dAdaptive");
        Formula repairBits = F.Id("dRepair");
        Formula depth = F.Id("d");
        Formula width = F.Id("k");
        Formula protocol = F.Id("pi");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula types = Seq(Operatorname, Grp(F.Id("Type")));
        Formula adaptiveWidths = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            Exists, Sp, protocol, Colon, Sp, Call("BinaryProtocol", state, depth),
            Comma, Sp, Call("IdentifiesGiven", current, target, protocol), CloseBrace);
        Formula repairWidths = Seq(
            OpenBrace, width, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            Call("BinaryRepairFeasible", current, target, width), CloseBrace);
        Formula optimum = Call("clog", D(2),
            Call("worstFiberDiversity", current, target));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coordinate, Comma, Sp, targetCarrier,
            Colon, Sp, types, Comma, RowBreak, Grp(),
            Fintype(state), Comma, Sp, Fintype(coordinate), Comma, RowBreak, Grp(),
            current, Colon, Sp, state, Sp, To, Sp, coordinate, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetCarrier, Comma,
            RowBreak, Grp(),
            Exists, Sp, adaptiveDepth, Comma, Sp, repairBits,
            Sp, InMacro, Sp, naturals, Comma, RowBreak, Grp(),
            Call("IsLeast", adaptiveWidths, adaptiveDepth), Sp, Land, RowBreak, Grp(),
            Call("IsLeast", repairWidths, repairBits), Sp, Land, RowBreak, Grp(),
            adaptiveDepth, Sp, Eq, Sp, repairBits, Sp, Land, RowBreak, Grp(),
            repairBits, Sp, Eq, Sp, optimum, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
