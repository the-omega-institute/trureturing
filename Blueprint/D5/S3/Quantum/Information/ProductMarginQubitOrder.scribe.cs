using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginQubitOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct pure-factor boundary", H("ProductMarginQubitOrder"), Blocks(
            Describe.Lean(DescribeId.Create("common-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_trace_bound"),
                H("The closed-disk common-trace bound"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("xC"), Comma, F.Id("zC"), Comma, F.Id("xD"), Comma, F.Id("zD")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(D(0), Le, F.Id("xC")), Land, Seq(F.Id("xC"), Lt, D(1)), Land, Seq(D(0), Le, F.Id("xD")), Land, Seq(F.Id("xD"), Lt, D(1)), Land, Seq(Seq(Seq(Open, Seq(F.Id("xC"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("zC"), Caret, Grp(D(2))), Close)), Le, D(1)), Land, Seq(Seq(Seq(Open, Seq(F.Id("xD"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("zD"), Caret, Grp(D(2))), Close)), Le, D(1)))), Implies, Seq(Forall, Sp, Seq(F.Id("K")), Colon, Call("Matrix", Call("Prod", Call("Fin", D(2)), Call("Fin", D(2))), Call("Prod", Call("Fin", D(2)), Call("Fin", D(2))), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Grp(Seq(Call("PosSemidef", F.Id("K")), Land, Seq(F.Id("K"), Le, Call("kron", Call("qubitMatrix", F.Id("xC"), F.Id("zC")), Call("qubitMatrix", F.Id("xD"), F.Id("zD")))), Land, Seq(F.Id("K"), Le, Call("kron", Call("qubitMatrix", F.Id("xC"), Seq(Minus, F.Id("zC"))), Call("qubitMatrix", F.Id("xD"), Seq(Minus, F.Id("zD"))))))), Implies, Seq(Call("re", Call("trace", F.Id("K"))), Le, Seq(Frac, Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, Seq(Frac, Grp(Seq(F.Id("zC"), Caret, Grp(D(2)))), Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(F.Id("xC"), Caret, Grp(D(2))), Close)))), Close), Times, Seq(Open, Seq(Frac, Grp(Seq(F.Id("zD"), Caret, Grp(D(2)))), Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(F.Id("xD"), Caret, Grp(D(2))), Close)))), Close)))), Close))), Grp(Seq(Seq(Open, D(1), Close), Plus, Seq(Open, Seq(Sqrt, Grp(Seq(Seq(Open, Seq(Frac, Grp(Seq(F.Id("zC"), Caret, Grp(D(2)))), Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(F.Id("xC"), Caret, Grp(D(2))), Close)))), Close), Times, Seq(Open, Seq(Frac, Grp(Seq(F.Id("zD"), Caret, Grp(D(2)))), Grp(Seq(Seq(Open, D(1), Close), Minus, Seq(Open, Seq(F.Id("xD"), Caret, Grp(D(2))), Close)))), Close)))), Close)))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For independent local closed-disk coordinates with nonnegative x less than one, every complex PSD common lower matrix K of the two actual product margins has trace at most (1-s)/(1+s), where s is the square root of the product of the two reliabilities z squared divided by one minus x squared. The proof constructs an explicit identity split and evaluates its quadratic energy. A zero denominator forces a pure local factor, handled by the annihilating split below. Neither K nor the individual product margins are required to be invertible, and K need not commute with them. The exceptional x=1 factors require the separate product-state entropy argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-common-lower"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_zero_of_pure_left"),
                H("The distinct pure-factor boundary"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("u")), Colon, Call("Level"), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("n")), Colon, Call("Type", F.Id("u")), Comma, Esc, Seq(Grp(Seq(Call("Fintype", F.Id("n")), Land, Call("DecidableEq", F.Id("n")))), Implies, Seq(Forall, Sp, Seq(F.Id("x"), Comma, F.Id("z")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(D(0), Le, F.Id("x")), Land, Seq(F.Id("x"), Lt, D(1)), Land, Seq(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)), Eq, D(1)))), Implies, Seq(Forall, Sp, Seq(F.Id("R"), Comma, F.Id("S")), Colon, Call("Matrix", F.Id("n"), F.Id("n"), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Forall, Sp, Seq(F.Id("K")), Colon, Call("Matrix", Call("Prod", Call("Fin", D(2)), F.Id("n")), Call("Prod", Call("Fin", D(2)), F.Id("n")), Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc, Seq(Grp(Seq(Call("PosSemidef", F.Id("K")), Land, Seq(F.Id("K"), Le, Call("kron", Call("qubitMatrix", F.Id("x"), F.Id("z")), F.Id("R"))), Land, Seq(F.Id("K"), Le, Call("kron", Call("qubitMatrix", F.Id("x"), Seq(Minus, F.Id("z"))), F.Id("S"))))), Implies, Seq(F.Id("K"), Eq, D(0))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For x nonnegative and less than one and x squared plus z squared equal to one, every PSD common lower matrix of the two stated tensor margins is zero. The other local matrices are arbitrary. An explicit complex split U+V=I annihilates the respective pure local margins. The split-energy bound then gives K at most zero, while positivity gives the reverse inequality. The argument does not invert K and imposes no commutation or real-entry restriction on it."))), DescribeRole.Theorem))));

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
