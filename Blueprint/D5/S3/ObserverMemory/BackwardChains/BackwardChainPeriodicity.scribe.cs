using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.BackwardChains;

internal sealed class BackwardChainPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite compatible backward chain exists exactly at a periodic point.",
        H("Backward Chain Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("infinite-backward-chain-iff-periodic"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity."
                        + "infinite_backward_chain_iff_periodic"),
                H("Infinite backward chains are exactly periodic points"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier and a self-map tau, an infinite backward "
                            + "chain is a natural-number-indexed family whose next state maps to "
                            + "the current state, with coordinate zero equal to the displayed point.")),
                    Paragraph(Text(
                        "The canonical backward-orbit theorem identifies coordinate-zero values "
                            + "of all such chains with the periodic-point subtype. Applying its "
                            + "coordinate periodicity and surjectivity clauses gives the two "
                            + "directions of the displayed equivalence directly.")),
                    Paragraph(Text(
                        "Repository search found the exact declaration "
                            + "BackwardOrbitCore.backward_orbit_eval_zero_bijective and applied "
                            + "it; no additional library theorem was needed."))),
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
        Formula finite = Seq(OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, carrier, CloseBracket);
        Formula chain = Apply(F.Id("InfiniteBackwardChain"), update, point);
        Formula periodic = Seq(
            point, Sp, InMacro, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("periodicPts"))), update));

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, finite, Comma, Esc,
            update, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            point, Colon, Sp, carrier, Comma, Esc,
            chain, Sp, Leftrightarrow, Sp, periodic, Dot));
    }
}
