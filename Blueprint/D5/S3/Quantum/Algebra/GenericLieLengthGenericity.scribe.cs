using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericLieLengthGenericityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GenericLieLengthGenericity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero polynomial determinant transfers one full-span tuple to almost every tuple.",
        H("GenericLieLengthGenericity"),
        Blocks(
            Describe.Lean(DescribeId.Create("jc-genericlielengthgenericity-ae-mvpolynomial-ne-zero"),
                DeclarationHandle.Create(Prefix + "ae_mvPolynomial_ne_zero"), H("ae_mvPolynomial_ne_zero"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero real multivariate polynomial vanishes only on a Lebesgue null set. The proof inducts on the number of variables and uses the finite univariate root set and the product-measure theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthgenericity-ae-span-top-of-witness"),
                DeclarationHandle.Create(Prefix + "ae_span_top_of_witness"), H("ae_span_top_of_witness"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One spanning tuple supplies coefficients for a determinant polynomial which evaluates to one. Its nonzero evaluations give full span for almost all tuples of real basis coordinates."))), DescribeRole.Theorem)),
        []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("MvPolynomial"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, F.Id("p"), Sp, Neq, Sp, D(0), Sp, To, Sp, new Formula.Power(Forall, F.Id("m")), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Named("MvPolynomial"), Sp, Dot, Sp, Named("eval"), Sp, F.Id("x"), Sp, F.Id("p"), Sp, Neq, Sp, D(0)));

    private static Formula Formula1() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("FiniteDimensional"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("d"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Named("Module"), Sp, Dot, Sp, Named("Basis"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("S0"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, F.Id("M"))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S0"), Sp, F.Id("L"), Sp, Eq, Sp, Qualified("Top", "top"), Sp, To, Sp, new Formula.Power(Forall, F.Id("m")), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"))), Sp, Mapsto, Sp, F.Id("b"), Sp, Dot, Sp, Named("equivFun"), Sp, Dot, Sp, Named("symm"), Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("i"))))), Sp, F.Id("L"), Sp, Eq, Sp, Qualified("Top", "top")));
}
