using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class TriangleFourSymbolNecessityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/TriangleFourSymbolNecessity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source-faithful four-symbol necessity core for the finite triangle equality fiber.",
        H("Triangle Four-Symbol Necessity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-likelihood-frame-four-support-lower-bound"),
                DeclarationHandle.Create(Module + "weighted_likelihood_frame_card_ge_four"),
                H("Three weighted likelihood directions require four outputs"),
                StatementSource.FromAuthor(FrameLowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frame is the actual equality-fiber likelihood data: a strictly positive "
                            + "output law, three centered likelihood directions, pairwise weighted "
                            + "orthogonality, and one nonzero direction for each source. The proof "
                            + "makes 1 and the three directions linearly independent in the finite "
                            + "output function space, so the output support has cardinality at least four.")),
                    Paragraph(Text(
                        "This is the dimension part of the source theorem. The stochastic-kernel "
                            + "derivation of the frame is deliberately a separate bridge obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-latin-square-parity"),
                DeclarationHandle.Create(Module + "binary_latin_square_is_xor"),
                H("Binary pair-readout tables are parity up to relabelling"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Injectivity of every binary row and column is the exact four-cell "
                            + "recoverability condition. Exhaustive kernel reduction proves that "
                            + "the third block bit is the XOR of the first two, up to one global bit "
                            + "relabeling.")),
                    Paragraph(Text(
                        "The hypotheses describe the actual block table obtained from the original "
                            + "source law; they do not assert conditional pairwise independence as a "
                            + "substitute for the full law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-block-cell-definition"),
                DeclarationHandle.Create(Module + "binaryBlockCell"),
                H("Original-source binary block cell law"),
                StatementSource.FromAuthor(BlockCellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The cell law is indexed by the original source alphabets. It retains "
                            + "arbitrary within-block source noise and all structural zeros; q_i are "
                            + "not collapsed to source alphabets of size two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-block-source-pair-marginal"),
                DeclarationHandle.Create(Module + "binary_block_source_pair_marginal"),
                H("The reconstructed original source has independent pair marginals"),
                StatementSource.FromAuthor(PairMarginalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing the full original three-source cell law over the third source "
                            + "gives the product of the two averaged block laws. This is the exact "
                            + "source-pair consequence used by the necessity reconstruction and "
                            + "keeps the original source alphabets and zeros visible."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula O => F.Id("O");
    private static Formula S1 => F.Id("S1");
    private static Formula S2 => F.Id("S2");
    private static Formula S3 => F.Id("S3");
    private static Formula Fm => F.Id("F");
    private static Formula Four => D(4);
    private static Formula Bool => F.Id("Bool");

    private static Formula FrameLowerBoundFormula() => Disp(Seq(
        Forall, Sp, O, Comma, Sp, Call("Fintype", O), Sp, Rightarrow, Sp,
        Forall, Sp, Fm, Colon, Call("TriangleLikelihoodFrame", O), Comma, Sp,
        Four, Sp, Le, Sp, Call("card", O), Dot));

    private static Formula ParityFormula() => Disp(Seq(
        Forall, Sp, F.Id("g"), Colon, Bool, To, Sp, Bool, To, Sp, Bool, Comma, Sp,
        Call("RowsInjective", F.Id("g")), Sp, Land, Sp,
        Call("ColumnsInjective", F.Id("g")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("c"), Colon, Bool, Comma, Sp,
        Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), Comma, Sp,
        Call("g", F.Id("u"), F.Id("v")), Sp, Eq, Sp,
        Call("xor", F.Id("c"), Call("xor", F.Id("u"), F.Id("v"))), Dot));

    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);

    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Prod(Formula a, Formula b) => Call("prod", a, b);
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, InMacro, Sp, type)), Sp, body);

    private static Formula SourceTypes() => Seq(
        Forall, Sp, S1, Comma, Sp, S2, Comma, Sp, S3, Comma, Sp, O, Comma, Sp);

    private static Formula BlockCellFormula() => Disp(Seq(
        SourceTypes(),
        Forall, Sp, F.Id("h"), Colon, Call("Bijection", Prod(Bool, Bool), O), Comma, Sp,
        Forall, Sp, F.Id("q1"), Colon, Prod(Bool, S1), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("q2"), Colon, Prod(Bool, S2), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("q3"), Colon, Prod(Bool, S3), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("x"), Colon, O, Comma, Sp,
        Forall, Sp, F.Id("s"), Colon, Prod(S1, Prod(S2, S3)), Comma, Sp,
        Call("binaryBlockCell", F.Id("h"), F.Id("q1"), F.Id("q2"), F.Id("q3"), F.Id("x"), F.Id("s")),
        Sp, Eq, Sp,
        SumOver(F.Id("u"), Bool,
            SumOver(F.Id("v"), Bool,
                Call("if", Equal(F.Id("x"), Apply(F.Id("h"), Pair(F.Id("u"), F.Id("v")))),
                    Seq(Fraction(1, 4), Sp, Apply(F.Id("q1"), Pair(F.Id("u"), Call("fst", F.Id("s")))),
                        Sp, Apply(F.Id("q2"), Pair(F.Id("v"), Call("fst", Call("snd", F.Id("s"))))),
                        Sp, Apply(F.Id("q3"), Pair(Call("xor", F.Id("u"), F.Id("v")),
                            Call("snd", Call("snd", F.Id("s"))))), D(0))))), Dot));

    private static Formula PairMarginalFormula() => Disp(Seq(
        Forall, Sp, S1, Comma, Sp, S2, Comma, Sp, S3, Comma, Sp,
        Call("Fintype", S3), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("q1"), Colon, Prod(Bool, S1), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("q2"), Colon, Prod(Bool, S2), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("q3"), Colon, Prod(Bool, S3), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("s1"), Colon, S1, Comma, Sp, Forall, Sp, F.Id("s2"), Colon, S2, Comma, Sp,
        Call("normalized", F.Id("q3")), Sp, Rightarrow, Sp,
        SumOver(F.Id("u"), Bool, SumOver(F.Id("v"), Bool,
            SumOver(F.Id("s3"), S3,
                Seq(Fraction(1, 4), Sp, Apply(F.Id("q1"), Pair(F.Id("u"), F.Id("s1"))), Sp,
                    Apply(F.Id("q2"), Pair(F.Id("v"), F.Id("s2"))), Sp,
                    Apply(F.Id("q3"), Pair(Call("xor", F.Id("u"), F.Id("v")), F.Id("s3"))))))),
        Sp, Eq, Sp,
        Seq(Open, Fraction(1, 2), Close, Sp,
            Open, Apply(F.Id("q1"), Pair(F.Id("false"), F.Id("s1"))), Sp, Plus, Sp,
                Apply(F.Id("q1"), Pair(F.Id("true"), F.Id("s1"))), Close, Sp,
            Open, Fraction(1, 2), Close, Sp,
            Open, Apply(F.Id("q2"), Pair(F.Id("false"), F.Id("s2"))), Sp, Plus, Sp,
                Apply(F.Id("q2"), Pair(F.Id("true"), F.Id("s2"))), Close), Dot));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Fraction(byte numerator, byte denominator) =>
        Seq(Frac, Grp(F.D(numerator)), Grp(F.D(denominator)));

}
