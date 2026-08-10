using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class WindowRegisterCrtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Observer/WindowRegisterCRT",
            "Coprime finite window clocks and shifts split into two exact CRT tensor factors."),
        H("Coprime Tensor Factorization of a Window Register"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("window-register-splits-over-two-coprime-factors"),
                H("A window register splits over two coprime factors"),
                LeanTheorem(
                    "D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition"),
                CrtDecompositionFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let m and n be positive coprime window cardinalities. The canonical " +
                        "Chinese remainder equivalence reindexes the global address space " +
                        "Z/(mn)Z as Z/mZ times Z/nZ.")),
                    Paragraph(Text(
                        "The left and right clock factors restrict the global mn-th-root phase " +
                        "to the two coordinate summands. Additivity of the inverse CRT map " +
                        "turns the global diagonal phase into the product of those two local " +
                        "phases, so the reindexed clock is their Kronecker product exactly.")),
                    Paragraph(Text(
                        "The inverse CRT map also carries a one-step cyclic difference to a " +
                        "one-step difference in each coordinate. Therefore the reindexed shift " +
                        "is the Kronecker product of the two frozen factor shifts. This theorem " +
                        "is the binary coprime decomposition step, applicable in particular to " +
                        "two distinct prime-power factors; it does not assert an iterated " +
                        "prime-power tower.")))))));

    private static Formula CrtDecompositionFormula() => Disp(Seq(
        Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close, Eq, D(1), Sp,
        Rightarrow, Sp,
        Open,
        Operatorname, Grp(F.Id("reindex")), Underscore, Grp(F.Id("CRT")),
        Open, F.Id("V"), Underscore, Grp(F.Id("mn")), Close,
        Comma, Sp,
        Operatorname, Grp(F.Id("reindex")), Underscore, Grp(F.Id("CRT")),
        Open, F.Id("U"), Underscore, Grp(F.Id("mn")), Close,
        Close, Sp, Eq, Sp,
        Open,
        Operatorname, Grp(F.Id("kron")), Open,
        F.Id("V"), Underscore, Grp(F.Id("m")), Caret, Grp(F.Id("CRT")),
        Comma, Sp,
        F.Id("V"), Underscore, Grp(F.Id("n")), Caret, Grp(F.Id("CRT")),
        Close,
        Comma, Sp,
        Operatorname, Grp(F.Id("kron")), Open,
        F.Id("U"), Underscore, Grp(F.Id("m")), Comma, Sp,
        F.Id("U"), Underscore, Grp(F.Id("n")), Close,
        Close, Dot));
}
