using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class AdaptiveResidueIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-state modular model is exactly identified by a two-step adaptive "
            + "protocol, while every exact static suite uses three sensors.",
        H("Adaptive Modular Identification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-step-adaptive-residue-identification"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification."
                        + "two_step_adaptive_residue_identification"),
                H("Adaptive identification is strictly cheaper than a fixed suite"),
                StatementSource.FromAuthor(IdentificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state carrier is exactly {0, 10, 15, 21}. The three Boolean "
                            + "readouts are constructed from reduction modulo 2, 3, and 5; on "
                            + "this carrier each observed remainder is zero or one.")),
                    Paragraph(Text(
                        "The protocol first reads sensor 2. A zero leaves states 0 and 10, "
                            + "which sensor 3 separates. A one leaves states 15 and 21, "
                            + "which sensor 5 separates. Its two-bit transcript is injective.")),
                    Paragraph(Text(
                        "Every protocol node is required to choose one of the supplied "
                            + "readouts. Cardinality rules out exact transcripts of depth zero "
                            + "or one, so the minimum adaptive depth is two.")),
                    Paragraph(Text(
                        "Each individual sensor merges a state pair. More generally, omitting "
                            + "sensor 2 merges 0 with 15, omitting sensor 3 merges 0 with 10, "
                            + "and omitting sensor 5 merges 15 with 21. Thus an injective fixed "
                            + "suite needs all three sensors."))),
                DescribeRole.Theorem))));

    private static Formula IdentificationFormula()
    {
        Formula state = F.Id("X");
        Formula sensor = F.Id("p");
        Formula point = F.Id("x");
        Formula protocol = F.Id("pi");
        Formula history = F.Id("h");
        Formula depth = F.Id("d");
        Formula sensors = Seq(OpenBrace, D(2), Comma, Sp, D(3), Comma, Sp, D(5), CloseBrace);
        Formula states = Seq(
            OpenBrace, D(0), Comma, Sp, D(1, 0), Comma, Sp, D(1, 5), Comma, Sp,
            D(2, 1), CloseBrace);
        Formula readout = new Formula.Subscript(F.Id("q"), sensor);
        Formula adaptiveDepth = new Formula.Subscript(F.Id("D"), F.Id("ad"));
        Formula staticDepth = new Formula.Subscript(F.Id("D"), F.Id("stat"));
        Formula adaptiveCost = Seq(
            adaptiveDepth, Open, state, Comma, Sp, F.Id("q"), Close);
        Formula staticCost = Seq(
            staticDepth, Open, state, Comma, Sp, F.Id("q"), Close);

        return Disp(new Formula.Aligned([
            Seq(
                state, Sp, Eq, Sp, states, Comma, Sp, sensor, Sp, InMacro, Sp, sensors,
                Comma, Sp, Call("q", sensor, point), Sp, Eq, Sp,
                Call("decide", Equal(Call("mod", point, sensor), D(1)))),
            Seq(
                Call("fiber", Call("q", D(2)), F.Id("false")), Sp, Eq, Sp,
                Seq(OpenBrace, D(0), Comma, Sp, D(1, 0), CloseBrace), Comma, Sp,
                Call("fiber", Call("q", D(2)), F.Id("true")), Sp, Eq, Sp,
                Seq(OpenBrace, D(1, 5), Comma, Sp, D(2, 1), CloseBrace)),
            Seq(
                Exists, Sp, protocol, Colon, Sp, Call("BinaryProtocol", state, D(2)),
                Comma, Sp, Call("UsesReadoutFamily", F.Id("q"), protocol), Sp, Land, Sp,
                Call("Injective", Call("transcript", protocol))),
            Seq(
                Call("question", protocol, D(0)), Sp, Eq, Sp, Call("q", D(2)),
                Comma, Sp, Call("question", protocol, D(1), history), Sp, Eq, Sp,
                Call("if", new Formula.Subscript(history, D(0)), Call("q", D(5)),
                    Call("q", D(3)))),
            Seq(
                Forall, Sp, sensor, Sp, InMacro, Sp, sensors, Comma, Sp,
                Neg, Call("Injective", readout), Comma, Sp,
                Forall, Sp, depth, Sp, Lt, Sp, D(2), Comma, Sp,
                Neg, Call("ExactAtDepth", F.Id("q"), depth)),
            Seq(
                adaptiveCost, Sp, Eq, Sp, D(2), Sp, Land, Sp,
                staticCost, Sp, Eq, Sp, D(3), Sp, Land, Sp,
                adaptiveCost, Sp, Lt, Sp, staticCost, Dot),
        ]));
    }
}
