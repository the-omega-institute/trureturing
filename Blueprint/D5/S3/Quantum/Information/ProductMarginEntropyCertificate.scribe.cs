using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginEntropyCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform high-reliability entropy certificate", H("ProductMarginEntropyCertificate"), Blocks(
            Describe.Lean(DescribeId.Create("binary-entropy-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginEntropyCertificate.binary_entropy_certificate"),
                H("A uniform high-reliability entropy certificate"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("s")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Frac, Grp(D(2)), Grp(D(3))), Le, F.Id("s")), Land, Seq(F.Id("s"), Le, D(1)))), Implies, Seq(Seq(Seq(Open, Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, F.Id("s"), Close))), Grp(Seq(Seq(Open, D(2), Close), Times, Seq(Open, F.Id("s"), Close)))), Close), Times, Seq(Open, Call("log", Seq(Frac, Grp(D(4, 0, 9, 6)), Grp(D(3, 1, 2, 5)))), Close)), Le, Seq(Seq(Open, Seq(Seq(Open, Call("log", D(2)), Close), Minus, Seq(Open, Call("h", Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, F.Id("s"), Close))), Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, F.Id("s"), Close))))), Close)), Close), Minus, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, D(3), Close), Minus, Seq(Open, Seq(Frac, Grp(D(2)), Grp(F.Id("s"))), Close)), Close), Times, Seq(Open, Seq(Seq(Open, Call("log", D(2)), Close), Minus, Seq(Open, Call("h", Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, F.Id("s"), Close))), Grp(D(2)))), Close)), Close)), Close)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("In both formulas h denotes Real.binEntropy with natural logarithms. For every s in the closed interval [2/3,1], the binary-entropy expression in the statement is bounded below by (1-s)/(2s) times log(4096/3125). The proof applies binary entropy concavity to b=(1-s)/2 and b/(1-b), and then uses monotonicity up to 1/5. The endpoints use the actual continuous binary entropy values; no logarithm of a zero probability is differentiated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("information-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginEntropyCertificate.information_budget_nonneg"),
                H("Combining the three information estimates"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("a"), Comma, F.Id("b"), Comma, F.Id("k"), Comma, F.Id("j"), Comma, F.Id("c"), Comma, F.Id("d")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(D(0), Le, F.Id("a")), Land, Seq(F.Id("a"), Le, D(1)), Land, Seq(D(0), Le, F.Id("b")), Land, Seq(F.Id("b"), Le, D(1)), Land, Seq(D(0), Le, F.Id("k")), Land, Seq(D(0), Le, F.Id("c")), Land, Seq(D(0), Le, F.Id("d")), Land, Seq(D(0), Le, F.Id("j")), Land, Seq(F.Id("k"), Le, Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, F.Id("a"), Close), Times, Seq(Open, F.Id("b"), Close)))), Close))), Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, F.Id("a"), Close), Times, Seq(Open, F.Id("b"), Close)))), Close))))), Land, Seq(F.Id("j"), Le, Seq(Seq(Open, F.Id("b"), Close), Times, Seq(Open, F.Id("c"), Close))), Land, Seq(F.Id("j"), Le, Seq(Seq(Open, F.Id("a"), Close), Times, Seq(Open, F.Id("d"), Close))), Land, Seq(F.Id("j"), Le, Seq(Seq(Open, Call("log", D(2)), Close), Minus, Seq(Open, Call("h", Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, F.Id("a"), Close), Times, Seq(Open, F.Id("b"), Close)))), Close))), Grp(D(2)))), Close))))), Implies, Seq(D(0), Le, Seq(Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Call("log", D(2)), Close), Minus, Seq(Open, Call("h", F.Id("k")), Close)), Close), Plus, Seq(Open, F.Id("c"), Close)), Close), Plus, Seq(Open, F.Id("d"), Close)), Close), Minus, Seq(Open, Seq(Seq(Open, D(3), Close), Times, Seq(Open, F.Id("j"), Close)), Close)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("The two independent reliabilities a and b range over the entire unit interval. The conclusion combines a common trace bound with the two cross-contraction bounds and the classical absolute information bound. At a or b equal to zero, nonnegativity forces j=0. Otherwise reciprocal reliabilities split the proof into the low and high cases. This is a sufficient scalar budget: a quantum application must derive every input bound from its actual state and entropy; this statement alone does not assert that application."))), DescribeRole.Theorem))));

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
