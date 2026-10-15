using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericLieLengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GenericLieLength.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/jiacapel2024genericlielength");
    private static readonly LibraryNoteRef Lloyd = LibraryNoteRef.Create("D5/L/QuantumBounds/lloydmaity2019quantumcontrol");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic Lie-length in the traceless skew-Hermitian matrix Lie algebra grows logarithmically for every fixed generator count at least two.",
        H("GenericLieLength"),
        Blocks(
            Describe.Lean(DescribeId.Create("jc-genericlielength-ae-mvpolynomial-ne-zero"),
                DeclarationHandle.Create(Prefix + "ae_mvPolynomial_ne_zero"), H("ae_mvPolynomial_ne_zero"),
                StatementSource.FromAuthor(PolynomialFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero real multivariate polynomial vanishes only on a Lebesgue null set. AnalyticOnNhd.eval_mvPolynomial gives analyticity, MvPolynomial.funext supplies a nonzero value, and AnalyticZeroSetNull.ae_ne_zero_of_analytic gives nonvanishing almost everywhere."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielength-ae-span-top-of-witness"),
                DeclarationHandle.Create(Prefix + "ae_span_top_of_witness"), H("ae_span_top_of_witness"),
                StatementSource.FromAuthor(SpanFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One spanning tuple supplies coefficients for a determinant polynomial which evaluates to one. Its nonzero evaluations give full span for almost all tuples of real basis coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielength-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("claim"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 6 (arXiv:2301.08241v3, p. 19): “Let S be a random Lie-generating set of su(n), then Lieℓ(S) = Θ(log n) almost surely.” The number g of generators is fixed, with g ≥ 2, and the positive real constants depend on g but not on n ≥ 2. Lie-length counts generator letters in right-nested brackets and cumulative layers. Filter.Eventually under suPairMeasure gives the source almost-sure qualifier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielength-result"),
                DeclarationHandle.Create(Prefix + "result"), H("result"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(Source, Lloyd),
                Blocks(Paragraph(Text("For each fixed g ≥ 2 the constants c = 1/log(g + 1) and C = 32/log 2 work. The anchored heap produces a spanning pair in 16(1 + Nat.log 2 (n − 1)) letters; the determinant argument gives the same bound almost everywhere. The word-count dimension bound gives the lower estimate. The optimal upper constant and Lloyd–Maity Conjecture III remain open."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("jia-capel-2023-generic-lie-length"), ResolutionKind.Proved))),
        []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() => Disp(
        Seq(Named("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(2), Sp, Leq, Sp, F.Id("g"), Sp, To, Sp, Exists, Sp, Parenthesized(Seq(F.Id("c"), Sp, F.Id("C"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("c"), Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("C"), Sp, Land, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(2), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Named("Filter"), Sp, Dot, Sp, Named("Eventually"), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("c"), Sp, Star, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Leq, Sp, Parenthesized(Seq(Named("lieLength"), Sp, F.Id("n"), Sp, Parenthesized(Seq(Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("image"), Sp, F.Id("S"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Land, Sp, Parenthesized(Seq(Named("lieLength"), Sp, F.Id("n"), Sp, Parenthesized(Seq(Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("image"), Sp, F.Id("S"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Leq, Sp, F.Id("C"), Sp, Star, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))))))), Sp, Parenthesized(Seq(Named("MeasureTheory"), Sp, Dot, Sp, Named("ae"), Sp, Parenthesized(Seq(Named("suPairMeasure"), Sp, F.Id("g"), Sp, F.Id("n")))))))));

    private static Formula Formula1() => Disp(
        Named("claim"));

    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula PolynomialFormula() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("MvPolynomial"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, F.Id("p"), Sp, Neq, Sp, D(0), Sp, To, Sp, new Formula.Power(Forall, F.Id("m")), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Named("MvPolynomial"), Sp, Dot, Sp, Named("eval"), Sp, F.Id("x"), Sp, F.Id("p"), Sp, Neq, Sp, D(0)));

    private static Formula SpanFormula() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("FiniteDimensional"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("d"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Named("Module"), Sp, Dot, Sp, Named("Basis"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("S0"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, F.Id("M"))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S0"), Sp, F.Id("L"), Sp, Eq, Sp, Qualified("Top", "top"), Sp, To, Sp, new Formula.Power(Forall, F.Id("m")), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"))), Sp, Mapsto, Sp, F.Id("b"), Sp, Dot, Sp, Named("equivFun"), Sp, Dot, Sp, Named("symm"), Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("i"))))), Sp, F.Id("L"), Sp, Eq, Sp, Qualified("Top", "top")));
}
