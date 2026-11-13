using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mehat;

internal sealed class OrthogonalityProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Mehat/OrthogonalityProducts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/mehat2026eulermagic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrarily many integer orthogonality factors can have pairwise distinct products of entry squares.",
        H("Integer orthogonality factors and square-product separation"),
        Blocks(
            Paragraph(Text(
                "Fin(n) is the finite type of integers from zero through n minus one. Matrix(m,n,R) is the type of R-valued matrices with row type m and column type n; matrix multiplication and transpose have their usual meanings. The symbol smul denotes integer scalar multiplication, and the typed matrix 1 is the identity. Function.Injective means that equality of outputs implies equality of the complete input functions. Every product below ranges over all indices in Fin(k), and its value is an integer. The implicit parameter R ranges over arbitrary universe levels; [CommRing(R)] is an anonymous commutative-ring instance.")),
            Describe.Lean(DescribeId.Create("mehat-problem92-statement"),
                DeclarationHandle.Create(Prefix + "Problem92"), H("Problem 9.2"),
                StatementSource.FromAuthor(Disp(Seq(
                    ProblemName(), Sp, Colon, Sp, Named("Prop"), Sp, Colon, Eq, Sp,
                    ProblemFormula()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural k there are k integer matrices of order three, each with a nonzero integer constant gamma and A times its transpose equal to gamma times the identity. The map from all functions choosing one of the nine entry positions in each factor to the product of those entry squares is injective. The matrices and constants may depend on k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mehat-quaternion-matrix"),
                DeclarationHandle.Create(Prefix + "quaternionMatrix"), H("Quaternion factors"),
                StatementSource.FromAuthor(Disp(QuaternionFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The classical quaternion rotation formula gives a polynomial matrix with orthogonality constant equal to the square of the sum of the four coordinate squares. Individual factors need not satisfy either Euler diagonal equation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mehat-problem92-factor-existence"),
                DeclarationHandle.Create(Prefix + "problem92"), H("Factors for every positive length"),
                StatementSource.FromAuthor(Disp(Seq(
                    Named("problem", D(9, 2)), Sp, Colon, Sp, ProblemName()))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any two different coordinate polynomials, an integer quaternion makes the first zero and the second nonzero. Thus no nonzero weighted difference of their squares vanishes identically. For equal coordinates, different nonzero old products also give a nonzero difference. The product of all collision polynomials and all entry polynomials is nonzero in the integer polynomial ring. MvPolynomial.funext implies that it is nonzero at some integer tuple. Appending this quaternion factor preserves nonzero entries and injectivity, so induction gives every finite length. The induction includes the empty tuple only as an auxiliary extension; Problem 9.2 asserts positive lengths. No coefficient-size bound, efficient construction, order-seven result, or full Euler-matrix theorem is asserted here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mehat-2026-problem-92-orthogonality-products"),
                    ResolutionKind.Proved))),
        []));

    private static Formula ProblemFormula()
    {
        Formula k = F.Id("k"), i = F.Id("i"), a = F.Id("A"), p = F.Id("p");
        Formula matrices = new Formula.TypeArrow(Fin(k), Matrix(Integers()));
        Formula constants = new Formula.TypeArrow(Fin(k), Integers());
        Formula choices = new Formula.TypeArrow(Fin(k), Par(Seq(Fin(D(3)), Sp, Times, Sp, Fin(D(3)))));
        Formula ai = Call(a, i);
        Formula orthogonality = All("i", Fin(k), And(
            Ne(Call(GammaLower, i), D(0)),
            Equal(Mul(ai, new Formula.Power(Par(ai), F.Id("T"))),
                Call(Named("smul"), Call(GammaLower, i),
                    Par(Seq(D(1), Sp, Colon, Sp, Matrix(Integers())))))));
        Formula position = Call(p, i);
        Formula entry = Call(ai,
            new Formula.Subscript(Par(position), D(1)),
            new Formula.Subscript(Par(position), D(2)));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(i, Sp, InMacro, Sp, Fin(k))), Sp,
            new Formula.Power(Par(entry), D(2)));
        Formula injective = Call(Seq(Named("Function"), Dot, Named("Injective")),
            Seq(Par(Seq(p, Sp, Colon, Sp, choices)), Sp, Mapsto, Sp, product));
        return All("k", Naturals(), Implies(Le(D(1), k),
            Seq(Exists, Sp, Par(Seq(a, Sp, Colon, Sp, matrices)), Sp,
                Par(Seq(GammaLower, Sp, Colon, Sp, constants)), Comma, Sp,
                And(Par(orthogonality), injective))));
    }

    private static Formula QuaternionFormula()
    {
        Formula r = F.Id("R"), a = F.Id("a");
        Formula x0 = Call(a, D(0)), x1 = Call(a, D(1)), x2 = Call(a, D(2)), x3 = Call(a, D(3));
        Formula s0 = Square(x0), s1 = Square(x1), s2 = Square(x2), s3 = Square(x3);
        Formula matrix = Seq(Begin, Grp(F.Id("pmatrix")),
            Sub(Sub(Add(s0, s1), s2), s3), Amp,
            Twice(Sub(Mul(x1, x2), Mul(x0, x3))), Amp,
            Twice(Add(Mul(x1, x3), Mul(x0, x2))), RowBreak,
            Twice(Add(Mul(x1, x2), Mul(x0, x3))), Amp,
            Sub(Add(Sub(s0, s1), s2), s3), Amp,
            Twice(Sub(Mul(x2, x3), Mul(x0, x1))), RowBreak,
            Twice(Sub(Mul(x1, x3), Mul(x0, x2))), Amp,
            Twice(Add(Mul(x2, x3), Mul(x0, x1))), Amp,
            Add(Sub(Sub(s0, s1), s2), s3),
            End, Grp(F.Id("pmatrix")));
        return Seq(Forall, Sp, OpenBrace, r, Sp, Colon, Sp,
            new Formula.Power(Named("Type"), Star), CloseBrace, Sp,
            OpenBracket, Call(Named("CommRing"), r), CloseBracket, Sp,
            Par(Seq(a, Sp, Colon, Sp, new Formula.TypeArrow(Fin(D(4)), r))), Comma, Sp,
            Equal(Par(Seq(Call(Named("quaternionMatrix"), a), Sp, Colon, Sp, Matrix(r))), matrix));
    }

    private static Formula Named(string name, params Formula[] suffix) =>
        Seq(Operatorname, Grp([F.Id(name), .. suffix]));
    private static Formula ProblemName() => Named("Problem", D(9, 2));
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Fin(Formula n) => Call(Named("Fin"), n);
    private static Formula Matrix(Formula r) => Call(Named("Matrix"), Fin(D(3)), Fin(D(3)), r);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Square(Formula x) => new Formula.Power(x, D(2));
    private static Formula Twice(Formula x) => Mul(D(2), Par(x));
}
