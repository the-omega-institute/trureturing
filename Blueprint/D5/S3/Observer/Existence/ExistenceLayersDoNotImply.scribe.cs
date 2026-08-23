using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Existence;

internal sealed class ExistenceLayersDoNotImplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite countermodels separate type, interface, causal, and record existence.",
        H("Existence Layers Do Not Imply One Another"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("type-existence-does-not-imply-distinguishable-existence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Existence/ExistenceLayersDoNotImply."
                        + "type_existence_does_not_imply_distinguishable_existence"),
                H("Type existence does not imply distinguishable existence"),
                StatementSource.FromAuthor(TypeWithoutDistinguishabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two Boolean states are genuinely different, so their distinction exists "
                            + "at the type level. A constant readout into the one-point type sends "
                            + "both states to the same output, so the interface cannot distinguish "
                            + "them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "distinguishable-existence-does-not-imply-causal-existence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Existence/ExistenceLayersDoNotImply."
                        + "distinguishable_existence_does_not_imply_causal_existence"),
                H("Distinguishable existence does not imply causal existence"),
                StatementSource.FromAuthor(DistinguishabilityWithoutCausalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The identity readout separates the two Boolean states at the present "
                            + "time. A constant update maps both states to false after one step, "
                            + "so every positive-time readout agrees and the distinction has no "
                            + "causal existence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("causal-existence-does-not-imply-record-existence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Existence/ExistenceLayersDoNotImply."
                        + "causal_existence_does_not_imply_record_existence"),
                H("Causal existence does not imply record existence"),
                StatementSource.FromAuthor(CausalityWithoutRecordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Identity dynamics preserve two distinct Boolean states, and the identity "
                            + "readout separates them after one positive-time step. A constant "
                            + "record into the one-point type is stable under those dynamics but "
                            + "assigns the same record to both states, so record existence fails."))),
                DescribeRole.Theorem))));

    private static Formula TypeWithoutDistinguishabilityFormula()
    {
        Formula xType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula readout = F.Id("q");

        return Disp(Seq(
            Exists, Sp, xType, Comma, Sp, outputType, Colon, Sp, Type(), Comma, Esc,
            x, Comma, Sp, y, Colon, Sp, xType, Comma, Esc,
            readout, Colon, Sp, FunctionType(xType, outputType), Comma, RowBreak,
            Call("TypeExistence", x, y), Sp, Land, Sp,
            Neg, Sp, Call("DistinguishableExistence", readout, x, y), Dot));
    }

    private static Formula DistinguishabilityWithoutCausalityFormula()
    {
        Formula xType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula update = F.Id("T");
        Formula readout = F.Id("q");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Exists, Sp, xType, Comma, Sp, outputType, Colon, Sp, Type(), Comma, Esc,
            update, Colon, Sp, FunctionType(xType, xType), Comma, Esc,
            readout, Colon, Sp, FunctionType(xType, outputType), Comma, Esc,
            x, Comma, Sp, y, Colon, Sp, xType, Comma, RowBreak,
            Call("DistinguishableExistence", readout, x, y), Sp, Land, Sp,
            Neg, Sp, Call("CausalExistence", update, readout, x, y), Dot));
    }

    private static Formula CausalityWithoutRecordFormula()
    {
        Formula xType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula recordType = F.Id("R");
        Formula update = F.Id("T");
        Formula readout = F.Id("q");
        Formula record = F.Id("record");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");

        return Disp(Seq(
            Exists, Sp, xType, Comma, Sp, outputType, Comma, Sp, recordType,
            Colon, Sp, Type(), Comma, Esc,
            update, Colon, Sp, FunctionType(xType, xType), Comma, Esc,
            readout, Colon, Sp, FunctionType(xType, outputType), Comma, Esc,
            record, Colon, Sp, FunctionType(xType, recordType), Comma, Esc,
            x, Comma, Sp, y, Colon, Sp, xType, Comma, RowBreak,
            Call("CausalExistence", update, readout, x, y), Sp, Land, Sp,
            Open, Forall, Sp, z, Comma, Sp,
            Call("record", Call("T", z)), Sp, Eq, Sp, Call("record", z), Close,
            Sp, Land, Sp,
            Neg, Sp, Call("RecordExistence", update, record, x, y), Dot));
    }

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula FunctionType(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
