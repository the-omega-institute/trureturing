using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginBlockStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual subnormalized block-state partial traces", H("ProductMarginBlockState"), Blocks(
            Describe.Lean(DescribeId.Create("block-partial-traces"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginBlockState.block_partial_traces"),
                H("Actual subnormalized block-state partial traces"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("u")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("n")), Colon, Call("Type", F.Id("u")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("n")), Land, Sp, Call("DecidableEq", F.Id("n")))), Implies, Sp, Seq(Forall, Sp, Seq(F.Id("P"), Comma, F.Id("Q"), Comma, F.Id("K")), Colon, Call("Matrix", F.Id("n"), F.Id("n"), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Seq(Call("traceA", Call("blockMatrix", F.Id("P"), F.Id("Q"), F.Id("K"))), Eq, Seq(Frac, Grp(Seq(Seq(Open, Call("kron", Call("pointer", D(0)), F.Id("P")), Close), Plus, Seq(Open, Call("kron", Call("pointer", D(1)), F.Id("Q")), Close))), Grp(D(2)))), Land, Sp, Seq(Call("traceB", Call("blockMatrix", F.Id("P"), F.Id("Q"), F.Id("K"))), Eq, Seq(Frac, Grp(Seq(Seq(Open, Call("kron", Call("pointer", D(0)), F.Id("P")), Close), Plus, Seq(Open, Call("kron", Call("pointer", D(1)), F.Id("Q")), Close))), Grp(D(2)))), Land, Sp, Seq(Call("traceAB", Call("blockMatrix", F.Id("P"), F.Id("Q"), F.Id("K"))), Eq, Seq(Frac, Grp(Seq(Seq(Open, F.Id("P"), Close), Plus, Seq(Open, F.Id("Q"), Close))), Grp(D(2)))), Land, Sp, Seq(Call("traceN", Call("blockMatrix", F.Id("P"), F.Id("Q"), F.Id("K"))), Eq, Call("diagonal", Call("blockTraces", F.Id("P"), F.Id("Q"), F.Id("K")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(Paragraph(Text("The four blocks are (P-K)/2, K/2, K/2 and (Q-K)/2. The blockState constructor proves positivity and trace one for density states P and Q and an arbitrary complex positive semidefinite common lower matrix K. Tracing out either classical bit gives the same two row sums P/2 and Q/2; tracing out both gives (P+Q)/2. Tracing out the quantum index gives a diagonal AB matrix whose entries are the actual block traces. For unit-trace P and Q, the entries are (1-k)/2, k/2, k/2 and (1-k)/2, with k equal to trace K. Zero blocks remain zero and are never normalized by their own trace. The formula uses traceA, traceB, traceAB and traceN for the indicated index contractions; blockTraces is the function (a,b) to trace(gamma(P,Q,K,a,b)). These partial-trace identities retain every zero block weight."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
