using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class AnchoredFlowEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anchored flow identity is characterized by enriched topological conjugacy.",
        H("Anchored Flow Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("anchored-flow-identity-is-enriched-conjugacy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/AnchoredFlowEquivalence."
                        + "anchored_flow_equivalence"),
                H("Anchored flow identity is enriched conjugacy"),
                StatementSource.FromAuthor(AnchoredEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A and B be compact connected Hausdorff carriers with continuous "
                            + "real flows, internally selected anchors, readouts, additive "
                            + "memory cocycles, and ledgers. Their primitive equivalence is "
                            + "constructed from a continuous bijection preserving each field.")),
                    Paragraph(Text(
                        "B belongs to the observer identity class of A exactly when a "
                            + "homeomorphism sends anchor to anchor, conjugates every time "
                            + "slice, preserves readout by composition, and transports both "
                            + "cocycle and ledger data. Every enriched anchored self-conjugacy "
                            + "fixes the internally selected anchor, so it lies in the anchor's "
                            + "stabilizer.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned "
                            + "isHomeomorph_iff_continuous_bijective as the exact bridge from "
                            + "the semantic continuous bijection to a homeomorphism. The Lean "
                            + "proof imports and applies that result directly."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Field(Formula owner, string name) =>
        Seq(owner, Dot, F.Id(name));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Apply(Apply(function, first), second);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula AnchoredEquivalenceFormula()
    {
        Formula carrierX = F.Id("X");
        Formula carrierY = F.Id("Y");
        Formula readoutType = F.Id("Q");
        Formula valueType = F.Id("V");
        Formula ledgerType = F.Id("L");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula h = F.Id("h");
        Formula g = F.Id("g");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula anchorA = Field(a, "anchor");
        Formula anchorB = Field(b, "anchor");
        Formula flowA = Field(a, "dynamics");
        Formula flowB = Field(b, "dynamics");
        Formula readoutA = Field(a, "readout");
        Formula readoutB = Field(b, "readout");
        Formula cocycleA = Field(a, "cocycle");
        Formula cocycleB = Field(b, "cocycle");
        Formula ledgerA = Field(a, "ledger");
        Formula ledgerB = Field(b, "ledger");
        Formula hx = Apply(h, x);
        Formula gx = Apply(g, x);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrierX, Comma, Sp, carrierY, Comma, Sp,
            readoutType, Comma, Sp, valueType, Comma, Sp, ledgerType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", carrierX), Comma, Sp,
            Typeclass("CompactSpace", carrierX), Comma, Sp,
            Typeclass("ConnectedSpace", carrierX), Comma, Sp,
            Typeclass("T2Space", carrierX), Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", carrierY), Comma, Sp,
            Typeclass("CompactSpace", carrierY), Comma, Sp,
            Typeclass("ConnectedSpace", carrierY), Comma, Sp,
            Typeclass("T2Space", carrierY), Comma, RowBreak, Grp(),
            Typeclass("AddCommMonoid", valueType), Comma, RowBreak, Grp(),
            a, Colon, Sp, Call("AnchoredFlow", carrierX, readoutType, valueType, ledgerType),
            Comma, Sp,
            b, Colon, Sp, Call("AnchoredFlow", carrierY, readoutType, valueType, ledgerType),
            Comma, RowBreak, Grp(),
            b, Sp, InMacro, Sp, Call("observerIdentity", a), Sp, Iff, Sp,
            Open, Exists, Sp, h, Colon, Sp,
            Call("Homeomorph", carrierX, carrierY), Comma, Esc,
            Apply(h, anchorA), Sp, Eq, Sp, anchorB, Sp, Land, RowBreak,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            x, Colon, Sp, carrierX, Comma, Sp,
            Apply(h, Apply2(flowA, t, x)), Sp, Eq, Sp,
            Apply2(flowB, t, hx), Close, Sp, Land, RowBreak,
            readoutB, Sp, Circ, Sp, h, Sp, Eq, Sp, readoutA, Sp, Land, RowBreak,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            x, Colon, Sp, carrierX, Comma, Sp,
            Apply2(cocycleB, t, hx), Sp, Eq, Sp,
            Apply2(cocycleA, t, x), Close, Sp, Land, RowBreak,
            ledgerB, Sp, Circ, Sp, h, Sp, Eq, Sp, ledgerA, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, g, Colon, Sp,
            Call("Homeomorph", carrierX, carrierX), Comma, Esc,
            Open, Apply(g, anchorA), Sp, Eq, Sp, anchorA, Sp, Land, Sp,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            x, Colon, Sp, carrierX, Comma, Sp,
            Apply(g, Apply2(flowA, t, x)), Sp, Eq, Sp,
            Apply2(flowA, t, gx), Close, Sp, Land, RowBreak,
            readoutA, Sp, Circ, Sp, g, Sp, Eq, Sp, readoutA, Sp, Land, Sp,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            x, Colon, Sp, carrierX, Comma, Sp,
            Apply2(cocycleA, t, gx), Sp, Eq, Sp,
            Apply2(cocycleA, t, x), Close, Sp, Land, Sp,
            ledgerA, Sp, Circ, Sp, g, Sp, Eq, Sp, ledgerA, Close,
            Sp, Rightarrow, Sp, Apply(g, anchorA), Sp, Eq, Sp, anchorA,
            Close, Dot, End, Grp(F.Id("gathered"))));
    }
}
