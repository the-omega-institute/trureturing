using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SimicWeightedPowerSumFloorIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/simic2007h655");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simic's weighted power-sum floor identity for at least two positive indices.",
        H("Simic H-655(ii) weighted power-sum floor identity"),
        Blocks(
            Node("simic_h655_ii", "The weighted power-sum floor identity",
                TheoremFormula(),
                "For a finite set of distinct positive natural indices with at least two "
                    + "members and a natural base at least two, the integer floor of the "
                    + "weighted power mean after multiplication by q minus one is one "
                    + "below the maximum-index multiple. Lean's Finset.max' supplies the "
                    + "maximum after its nonemptiness proof. The proof centers at the maximum "
                    + "index: a second index makes the deficit positive, while the closed "
                    + "tail identity and subset domination bound it by one. The singleton "
                    + "endpoint has floor c(q - 1), so it is outside this statement. Part 1 "
                    + "of the printed problem is not formalized.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("simic-h655-ii-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula TheoremFormula()
    {
        var s = F.Id("s");
        var i = F.Id("i");
        var q = F.Id("q");
        var card = QualifiedCall("Finset", "card", s);
        var cardBound = Relation(D(2), FormulaRelationOperator.LessThanOrEqual, card);
        var positive = ForAll("i", Naturals(),
            Implies(Member(i, s), Relation(D(1), FormulaRelationOperator.LessThanOrEqual, i)));
        var baseBound = Relation(D(2), FormulaRelationOperator.LessThanOrEqual, q);
        var conclusion = new Formula.Relation(WeightedFloor(s, q),
            FormulaRelationOperator.Equal, RightHandSide(s, q));
        return Disp(ForAll("s", Call("Finset", Naturals()),
            Parenthesized(Implies(cardBound,
                Parenthesized(Implies(positive,
                    ForAll("q", Naturals(),
                        Parenthesized(Implies(baseBound, conclusion)))))))));
    }

    private static Formula WeightedFloor(Formula s, Formula q)
    {
        var qRat = Coerce(q, Rationals());
        var index = F.Id("i");
        var numerator = SumOver(index, s,
            Mul(Coerce(index, Rationals()), Power(qRat, index)));
        var denominator = SumOver(index, s, Power(qRat, index));
        return new Formula.Floor(Div(Mul(Sub(qRat, D(1)), numerator), denominator));
    }

    private static Formula RightHandSide(Formula s, Formula q)
    {
        var qInt = Coerce(q, Integers());
        var maximum = QualifiedCall("Finset", "max", s);
        return Sub(Mul(Coerce(maximum, Integers()), Sub(qInt, D(1))), D(1));
    }

    private static Formula SumOver(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, set)), Sp, body);

    private static Formula QualifiedCall(string prefix, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);

    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(basis, exponent);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Rationals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("Q")]));

    private static Formula Integers() => new Formula.Integers();
}
