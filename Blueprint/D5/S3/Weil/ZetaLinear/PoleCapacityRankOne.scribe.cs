using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class PoleCapacityRankOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive rank-one pole update removes at most one negative direction.",
        H("Pole Capacity Rank One"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-pole-pair-removes-at-most-one-negative-direction"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.pole_capacity_rank_one"),
                H("A pole pair has negative-index capacity one"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I be a finite carrier with decidable equality, let F0 be a "
                            + "Hermitian complex matrix on I, and let p be a complex vector. "
                            + "The updated matrix is constructed as F0 plus twice the canonical "
                            + "outer product of p with its conjugate.")),
                    Paragraph(Text(
                        "The negative spectral index of the update is at least the original "
                            + "negative index minus one. If the updated matrix is positive "
                            + "semidefinite, the original negative index is therefore at most "
                            + "one.")),
                    Paragraph(Text(
                        "The proof applies negative-index subadditivity to the updated matrix "
                            + "and the negative rank-one correction. Pinned Mathlib supplies "
                            + "the outer-product positivity and rank bound; repository searches "
                            + "found no theorem already stating both public clauses."))),
                DescribeRole.Theorem),
            Publication0(), Publication1())));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula baseMatrix = F.Id("F0");
        Formula poleVector = F.Id("p");
        Formula type = Call("Type");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", index, index, complex);
        Formula vector = Arrow(index, complex);
        Formula correction = Multiply(
            D(2),
            Call("vecMulVec", poleVector, Call("star", poleVector)));
        Formula updatedMatrix = Add(baseMatrix, correction);
        Formula assumptions = And(
            Call("Fintype", index),
            And(
                Call("DecidableEq", index),
                Call("Hermitian", baseMatrix)));
        Formula capacity = LessOrEqual(
            Subtract(Call("negIndex", baseMatrix), D(1)),
            Call("negIndex", updatedMatrix));
        Formula positiveConsequence = Implies(
            Call("PosSemidef", updatedMatrix),
            LessOrEqual(Call("negIndex", baseMatrix), D(1)));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("F0", matrix),
                Bound("p", vector),
            ],
            Implies(assumptions, And(capacity, positiveConsequence)));
    }

    private static DocumentBlock Publication0() =>
        Describe.Lean(DescribeId.Create("publication-rank-hermnegpart-eq-negindex"),
            DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.rank_hermNegPart_eq_negIndex"), H("rank hermNegPart eq negIndex"),
            StatementSource.FromAuthor(Disp(PublicationFormula0())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The negative spectral part has rank equal to the number of negative eigenvalues."))), DescribeRole.Theorem);
    private static Formula PublicationFormula0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, F.Id("n"), Sp, Colon, Sp, F.Id("Type"))), Sp, Seq(OpenBracket, Seq(F.Id("RCLike"), Sp, F.Id("K")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("n")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("n")), CloseBracket), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("n"), Sp, F.Id("n"), Sp, F.Id("K"))), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("hermNegPart"), Sp, F.Id("hA"))), Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("negIndex"), Sp, F.Id("hA"));

    private static DocumentBlock Publication1() =>
        Describe.Lean(DescribeId.Create("publication-negdefon-range-hermnegpart"),
            DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.negDefOn_range_hermNegPart"), H("negDefOn range hermNegPart"),
            StatementSource.FromAuthor(Disp(PublicationFormula1())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The negative of a Hermitian matrix is positive definite on the range of its negative spectral part."))), DescribeRole.Theorem);
    private static Formula PublicationFormula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, F.Id("n"), Sp, Colon, Sp, F.Id("Type"))), Sp, Seq(OpenBracket, Seq(F.Id("RCLike"), Sp, F.Id("K")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("n")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("n")), CloseBracket), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("n"), Sp, F.Id("n"), Sp, F.Id("K"))), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("PosDefOn"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("LinearMap"), Sp, Dot, Sp, F.Id("range"), Sp, Parenthesized(Seq(F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("hermNegPart"), Sp, F.Id("hA"))), Sp, Dot, Sp, F.Id("mulVecLin"))));

    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
}
