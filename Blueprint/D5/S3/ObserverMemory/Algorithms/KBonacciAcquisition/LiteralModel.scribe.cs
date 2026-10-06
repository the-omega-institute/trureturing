using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class LiteralModelDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original KBonacci weights, literal bit execution, and joint actual-history realization.",
        H("LiteralModel"),
        Blocks(
            Paragraph(Text(
                "Fix an original order k at least two. LiveRecord has value in ZMod 2, "
                    + "ambient phase in ZMod (k+1), and a natural tail. The legal-tail "
                    + "premise is tail below k. Rejection is none and is absorbing. "
                    + "A false bit advances phase and clears tail; a true bit adds the "
                    + "coefficient at the old phase and increments tail, rejecting when "
                    + "the new tail reaches k. coefficient is one precisely at phases "
                    + "zero and minus one, and zero elsewhere. runBits uses the native "
                    + "chronological runWord. endpointReading offers only the resulting "
                    + "value or rejection after the entire supplied word.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-literal-block-execution"),
                DeclarationHandle.Create(Owner + "literal_block_execution"),
                H("Old-tail scanning and literal endpoint updates agree"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("w"), Colon, Sp, Seq(Call("Fin", F.Id("n")), Sp, To, Sp, Seq(Operatorname,
                    Grp(F.Id("Bool")))), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi"), Colon, Sp,
                    Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open,
                    Seq(F.Id("s"), Sp, Lt, Sp, F.Id("k")), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Seq(Open, Seq(Call("runBits",
                    F.Id("k"), F.Id("w"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))), Sp, Eq, Sp, Call("if", Seq(Call("runAdmissible",
                    Seq(F.Id("k"), Minus, D(1)), Seq(Seq(F.Id("k"), Minus, D(1)), Minus, F.Id("s")), F.Id("n"), F.Id("w")), Sp,
                    Eq, Sp, Seq(Operatorname, Grp(F.Id("true")))), Call("some", Seq(F.Id("v"), Plus, Call("wordIncrement", F.Id("k"),
                    F.Id("phi"), F.Id("w"))), Seq(F.Id("phi"), Plus, F.Id("n")), Call("tailAfter", F.Id("s"), F.Id("w"))), Seq(Operatorname,
                    Grp(F.Id("none"))))), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open, Seq(Call("runAdmissible", Seq(F.Id("k"),
                    Minus, D(1)), Seq(Seq(F.Id("k"), Minus, D(1)), Minus, F.Id("s")), F.Id("n"), F.Id("w")), Sp, Eq, Sp, Seq(Operatorname,
                    Grp(F.Id("true")))), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("tailAfter", F.Id("s"), F.Id("w")), Sp, Lt,
                    Sp, F.Id("k")), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quantify over every natural k at least two, every natural n, "
                        + "every Boolean word w on Fin n, every value v in ZMod 2, "
                        + "every ambient phase phi in ZMod (k+1), and every natural "
                        + "s below k. accepted(w) means the native runAdmissible "
                        + "scanner with maxTrue=k-1 and fuel=k-1-s returns true. "
                        + "scanResult is none on failure, and otherwise is the live "
                        + "record (v+wordIncrement(k,phi,w),phi+n,tailAfter(s,w)). "
                        + "wordIncrement sums the coefficient at each actual position "
                        + "whose bit is true. tailAfter performs the chronological "
                        + "tail updates. Execution equals scanResult, and acceptance "
                        + "implies tailAfter(s,w) below k. No bit within a block is "
                        + "added to the observation interface."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-joint-live-history-realization"),
                DeclarationHandle.Create(Owner + "joint_history_realization"),
                H("One actual legal word realizes all live coordinates"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi"), Colon, Sp, Call("ZMod",
                    Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp,
                    Leq, Sp, F.Id("m")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land,
                    Sp, Seq(Open, Call("divides", Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi"))),
                    Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Exists, Sp, F.Id("N"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, F.Id("w"), Colon, Sp, Seq(Call("Fin", F.Id("N")), Sp, To, Sp, Seq(Operatorname, Grp(F.Id("Bool")))),
                    Comma, Sp, Seq(Open, Seq(Seq(Open, Call("divides", F.Id("m"), F.Id("N")), Close), Sp, Land, Sp, Seq(Open,
                    Call("DBonacciAdmissible", F.Id("k"), F.Id("N"), F.Id("w")), Close), Sp, Land, Sp, Seq(Open, Seq(Call("runBits",
                    F.Id("k"), F.Id("w"), Call("some", D(0), D(0), D(0))), Sp, Eq, Sp, Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Call("originalWordValue", F.Id("k"), F.Id("w")), Sp, Eq, Sp, F.Id("v")),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Call("tailAfter", D(0), F.Id("w")), Sp, Eq, Sp, F.Id("s")), Close), Sp,
                    Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Seq(Seq(Open, Seq(F.Id("j"), Plus, D(1)), Close), Sp, Cdot, Sp, F.Id("m")), Sp, Leq, Sp,
                    F.Id("N")), Close), Sp, Implies, Sp, Seq(Open, Call("DBonacciAdmissible", F.Id("k"), F.Id("m"), Seq(LambdaLower,
                    Sp, F.Id("i"), Colon, Sp, Call("Fin", F.Id("m")), Comma, Sp, Call("w", Seq(Seq(F.Id("j"), Sp, Cdot, Sp, F.Id("m")),
                    Plus, Call("val", F.Id("i")))))), Close)), Close)), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural k at least two, positive natural m, "
                            + "value v in ZMod 2, ambient phase phi in ZMod (k+1), "
                            + "and natural tail s below k, assume gcd(m,k+1) divides "
                            + "the natural representative phi.val. There exist one "
                            + "natural N and one word w on Fin N such that m divides "
                            + "N, w is DBonacciAdmissible, its execution from the "
                            + "empty record is exactly (v,phi,s), its originalWordValue "
                            + "is v, and tailAfter(0,w) is s. For every natural j "
                            + "with (j+1)m at most N, the length-m subword at positions "
                            + "jm through (j+1)m-1 is DBonacciAdmissible as well.")),
                    Paragraph(Text(
                        "The construction applies the generalized natural CRT to "
                            + "the compatible residues zero modulo m and phi.val "
                            + "modulo k+1, then enlarges that same length. The witness "
                            + "is a first bit v+d, followed by N-s-1 zero bits and s "
                            + "one bits; d is the coefficient sum at those final s "
                            + "positions. The value, phase, tail and all local blocks "
                            + "therefore concern the same word. These statements "
                            + "supply live source records. Rejected-source realization, "
                            + "phase acquisition, the full first-zero recursion "
                            + "and the full adaptive acquisition iff and cost bound "
                            + "require their own mathematical conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
