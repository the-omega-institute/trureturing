using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.FactorWidth;

internal sealed class NonnegativeFactorWidthTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entrywise nonnegative matrices of complex factor width at most two admit bounded nonnegative real decompositions.",
        H("Nonnegative real factors from complex two-sparse factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonnegative-two-sparse-gram"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurement/FactorWidth/NonnegativeFactorWidthTwo.nonnegative_two_sparse_gram"),
            H("Bounded nonnegative two-sparse Gram decomposition"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The input is a real square matrix X with nonnegative entries. Its entrywise complex "
                    + "coercion admits a finite sum of complex Hermitian outer products, each on at most two "
                    + "coordinates. The conclusion preserves the full matrix and bounds the number of "
                    + "entrywise nonnegative real factors, each supported on at most two coordinates.")),
                Paragraph(Text(
                    "Group the input factors by exact two-element support. For one pair, let A and B be the "
                    + "sums of squared norms at its endpoints and let c be the corresponding entry of X. "
                    + "Cauchy–Schwarz gives c squared at most A times B. For A positive, use the entries "
                    + "sqrt(A) and c / sqrt(A). For A zero, c is zero and the pair can contribute zero. "
                    + "The new factor preserves the cross entry and consumes at most each diagonal budget.")),
                Paragraph(Text(
                    "Exact support groups are disjoint, so total diagonal consumption is at most the original "
                    + "diagonal. One singleton factor at each vertex supplies the difference. This uses one "
                    + "slot per unordered pair and one per vertex, allowing zero factors."))),
            DescribeRole.Theorem))));

    private static Formula Named(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, JoinArgs(args), Close);

    private static Formula JoinArgs(Formula[] args) =>
        Seq([.. args.SelectMany((arg, index) =>
            index == 0 ? new[] { arg } : new[] { Comma, Sp, arg })]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Quantified(Formula quantifier, Formula name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var matrix = F.Id("X");
        var k = F.Id("k");
        var v = F.Id("v");
        var t = F.Id("t");
        var i = F.Id("i");
        var j = F.Id("j");
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var coordinate = Named("Fin", n);
        var factor = Named("Fin", k);
        var realMatrix = Named("Matrix", coordinate, coordinate, real);
        var vector = Seq(coordinate, Sp, To, Sp, real);
        var family = Seq(factor, Sp, To, Sp, vector);
        var vt = Seq(v, Underscore, Grp(t));
        var vti = Seq(vt, Parenthesized(i));
        var entry = Seq(matrix, Parenthesized(Seq(i, Comma, j)));
        var inputNonneg = Quantified(Forall, i, coordinate,
            Quantified(Forall, j, coordinate, Seq(D(0), Sp, Leq, Sp, entry)));
        var inputGram = Named("IsKIncoherentSum", D(2), Named("complex", matrix));
        var count = Seq(k, Sp, Leq, Sp,
            new Formula.Binary(n, FormulaBinaryOperator.Add, Named("choose", n, D(2))));
        var nonneg = Quantified(Forall, t, factor,
            Quantified(Forall, i, coordinate, Seq(D(0), Sp, Leq, Sp, vti)));
        var support = Quantified(Forall, t, factor,
            Seq(Named("card", Named("supp", vt)), Sp, Leq, Sp, D(2)));
        var outer = Seq(vt, Sp, new Formula.Power(vt, F.Id("T")));
        var index = Grp(Seq(t, Sp, InMacro, Sp, factor));
        var gram = Seq(matrix, Sp, Eq, Sp, Sum, Underscore, index, Sp, outer);
        var conclusion = Seq(count, Sp, Land, Sp, Parenthesized(nonneg), Sp, Land, Sp,
            Parenthesized(support), Sp, Land, Sp, gram);
        return Disp(Quantified(Forall, n, nat, Quantified(Forall, matrix, realMatrix,
            Seq(Parenthesized(inputNonneg), Sp, To, Sp, inputGram, Sp, To, Sp,
                Quantified(Exists, k, nat, Quantified(Exists, v, family, conclusion))))));
    }
}
