using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockSugawaraSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.";

    private static Formula Bound() => Call("N", F.Id("p"));
    private static Formula Pair() => Call("normalPair", Seq(F.Id("n"), Minus, F.Id("k")),
        F.Id("k"), F.Id("p"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The polynomial Fock action has an explicit state-dependent finite support interval for its normal-ordered quadratic field.",
        H("Polynomial Fock Sugawara Support"),
        Blocks(
            Paragraph(Text("Let F be the complex polynomial algebra in variables X_k. Positive "
                + "Heisenberg modes act by (k+1) times partial differentiation in X_k, negative "
                + "modes by multiplication by X_k, and the zero mode vanishes. The current is "
                + "the Laurent field assembled from these modes. For a state p, N(p) is two "
                + "more than the largest variable index occurring in p; the supremum of the "
                + "empty variable set is zero.")),
            Describe.Lean(
                DescribeId.Create("normal-pair-support-interval"),
                DeclarationHandle.Create(Prefix + "normalPair_support_interval"),
                H("Normal-ordering has explicit polynomial support"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp,
                    F.Id("p"), InMacro, Sp, F.Id("F"), Comma, Esc,
                    Call("supp", Seq(F.Id("k"), Mapsto, Pair())), Sp, Subseteq, Sp,
                    Open, F.Id("n"), Minus, Bound(), Comma, Bound(), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A mode beyond N(p) differentiates in a variable absent "
                    + "from p and therefore vanishes. Normal ordering makes the larger of the "
                    + "two mode indices act first. A surviving summand consequently has both "
                    + "indices below N(p), which places k strictly inside the displayed interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sugawara-interval-sum"),
                DeclarationHandle.Create(Prefix + "L_interval_sum"),
                H("Finite intervals compute the Sugawara action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, F.Id("a"), Comma, F.Id("b"),
                    InMacro, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp,
                    F.Id("p"), InMacro, Sp, F.Id("F"), Comma, Esc,
                    F.Id("a"), Leq, Sp, F.Id("n"), Minus, Bound(), Sp, Land, Sp,
                    Bound(), Leq, Sp, F.Id("b"), Sp, Rightarrow, Sp,
                    Call("L", F.Id("n"), F.Id("p")), Eq,
                    Seq(D(2), Caret, Grp(Minus, D(1))), Sp, Sum,
                    Underscore, Grp(F.Id("k"), Eq, F.Id("a")), Caret, Grp(F.Id("b")),
                    Pair()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise finite normal-ordered sum defines L_n. "
                    + "Any closed integer interval containing its explicit support produces "
                    + "the same value on p. The theorem applies to every polynomial state and "
                    + "every integer mode, without asserting the Virasoro commutator."))),
                DescribeRole.Theorem))));
}
