using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.BackwardChains;

internal sealed class BackwardChainLayerPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinite backward chains and every predecessor layer characterize periodic points.",
        H("Backward Chain And Layer Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("backward-chain-and-layer-iff-periodic"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/BackwardChains/BackwardChainLayerPeriodicity."
                        + "backward_chain_and_layer_iff_periodic"),
                H("Backward chains and all predecessor layers are exactly periodic points"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier and a self-map tau, the predecessor layer at depth k "
                            + "is the set of states x satisfying tau iterated k times at x equals y. The "
                            + "public theorem states both the infinite compatible backward-chain equivalence "
                            + "and the arbitrary-depth nonempty-layer equivalence.")),
                    Paragraph(Text(
                        "The chain equivalence is imported from the canonical backward-chain theorem. For "
                            + "the layer direction, a layer at the carrier cardinality lies in the stabilized "
                            + "iterate range, whose canonical finite-image theorem identifies that range with "
                            + "the periodic-point set. A canonical backward orbit supplies a witness in every "
                            + "layer for the converse.")),
                    Paragraph(Text(
                        "Repository search found and directly applied the exact declarations "
                            + "BackwardChainPeriodicity.infinite_backward_chain_iff_periodic, "
                            + "BackwardOrbitCore.backward_iterate_apply, and "
                            + "StableImagePeriodicCore.iterate_range_card_antitone_and_stable. Pinned Mathlib "
                            + "search found the applied periodic-point and finite-pigeonhole ingredients; no "
                            + "single library theorem packaged both public equivalences."))),
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

    private static Formula Formula()
    {
        Formula carrier = F.Id("Y");
        Formula update = F.Id("tau");
        Formula point = F.Id("y");
        Formula depth = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finite = Seq(OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, carrier, CloseBracket);
        Formula chain = Apply(F.Id("InfiniteBackwardChain"), update, point);
        Formula periodic = Seq(
            point, Sp, InMacro, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("periodicPts"))), update));
        Formula layer = Apply(F.Id("PredecessorLayer"), update, point, depth);
        Formula nonemptyLayer = Apply(Seq(Operatorname, Grp(F.Id("Nonempty"))), layer);
        Formula allLayers = Seq(
            Forall, Sp, depth, InMacro, Sp, naturals, Comma, Esc, nonemptyLayer);

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, finite, Comma, Esc,
            update, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            point, Colon, Sp, carrier, Comma, Esc,
            Open, chain, Sp, Leftrightarrow, Sp, periodic, Close, Sp, Land, Sp,
            Open, allLayers, Sp, Leftrightarrow, Sp, periodic, Close, Dot));
    }
}
