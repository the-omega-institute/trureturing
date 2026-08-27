using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class CompactSignatureRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite compatibility of continuous protocol readouts on a compact state space has one global realization.",
        H("Compact Signature Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-compatibility-global-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Prediction/CompactSignatureRealization."
                        + "finite_compatibility_global_realization"),
                H("Finite compatibility gives a global realizing state"),
                StatementSource.FromAuthor(RealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "P is the protocol carrier, X is the compact state carrier, and Lambda "
                            + "assigns a Hausdorff output carrier to each protocol. Each protocol "
                            + "readout is continuous, and signature selects its prescribed value.")),
                    Paragraph(Text(
                        "Finite compatibility says that every finite protocol set has a common "
                            + "realizing state. The corresponding coordinate fibers are closed, "
                            + "so compactness supplies a point in their full intersection."))),
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

    private static Formula Typeclass(Formula property) =>
        Seq(OpenBracket, property, CloseBracket);

    private static Formula RealizationFormula()
    {
        Formula protocol = F.Id("P");
        Formula state = F.Id("X");
        Formula outputFamily = Lambda;
        Formula p = F.Id("p");
        Formula finiteProtocols = F.Id("F");
        Formula x = F.Id("x");
        Formula readout = F.Id("e");
        Formula signature = LambdaLower;
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula protocolOutput = Seq(outputFamily, Open, p, Close);
        Formula readoutAt = Seq(readout, Open, p, Close, Open, x, Close);
        Formula signatureAt = Seq(signature, Open, p, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, protocol, Comma, Sp, state, Colon, Sp, type, Comma, Sp,
            outputFamily, Colon, Sp, protocol, Sp, To, Sp, type, Comma,
            RowBreak, Grp(),
            Typeclass(Call("TopologicalSpace", state)), Comma, Sp,
            Typeclass(Call("CompactSpace", state)), Comma,
            RowBreak, Grp(),
            Typeclass(Seq(Forall, Sp, p, Colon, Sp, protocol, Comma, Sp,
                Call("TopologicalSpace", protocolOutput))), Comma, Sp,
            Typeclass(Seq(Forall, Sp, p, Colon, Sp, protocol, Comma, Sp,
                Call("T2Space", protocolOutput))), Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Open, p, Colon, Sp, protocol, Close, Sp, To, Sp,
            Call("ContinuousMap", state, protocolOutput), Comma,
            RowBreak, Grp(),
            signature, Colon, Sp, Open, p, Colon, Sp, protocol, Close, Sp, To, Sp,
            protocolOutput, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, finiteProtocols, Colon, Sp, Call("Set", protocol), Comma, Sp,
            Call("Finite", finiteProtocols), Sp, Rightarrow, Sp,
            Exists, Sp, x, Colon, Sp, state, Comma, Sp,
            Forall, Sp, p, InMacro, Sp, finiteProtocols, Comma, Sp,
            readoutAt, Sp, Eq, Sp, signatureAt, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Sp, x, Colon, Sp, state, Comma, Sp,
            Forall, Sp, p, Colon, Sp, protocol, Comma, Sp,
            readoutAt, Sp, Eq, Sp, signatureAt, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
