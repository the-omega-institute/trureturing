using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubtreePolynomial;

internal sealed class BrownMolConjecture42RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/brownmol2018subtree");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 206-vertex tree has a subtree root strictly inside the inner circle of the Brown–Mol annulus.",
        H("Brown–Mol Conjecture 4.2 and the subtree root of a 206-vertex tree"),
        Blocks(
            Describe.Lean(DescribeId.Create("brown-mol-subtree-polynomial"),
                DeclarationHandle.Create(Prefix + "subtreePolynomial"),
                H("The subtree polynomial"),
                StatementSource.FromAuthor(PolynomialFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "In Lean, P_G(z) evaluates subtreePolynomial G at z. ConnectedSubsets(G) consists of "
                    + "the nonempty vertex sets S for which the induced graph G[S] is connected. Each set "
                    + "contributes once. For a tree these are exactly its subtrees."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("brown-mol-conjecture-42"),
                DeclarationHandle.Create(Prefix + "Conjecture42"),
                H("The proposed translated annulus"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Brown and Mol state Conjecture 4.2 on p. 14 of arXiv:1810.08655v1. "
                    + "“If T is a tree of order n ≥ 2, then the subtree roots of T are contained in the annulus” "
                    + "shown above. Both endpoints are inclusive. FiniteTree ranges over simple graphs with "
                    + "a Fintype vertex instance and the IsTree property. Here n(T) is the vertex cardinality. "
                    + "Lean takes the natural predecessor before casting to the reals and uses real division "
                    + "and real exponentiation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("brown-mol-inner-bound-refutation"),
                DeclarationHandle.Create(Prefix + "conjecture42_false"),
                H("A root strictly inside the inner circle"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("Conjecture42")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The witness tree T has a hub and 41 branch "
                        + "centers, each with four private leaves. The connected sets comprise those containing "
                        + "the hub, those in one branch containing its center, and singleton leaves. Their "
                        + "contributions give the factorization P_T(z) = zF(z).")),
                    new DocumentBlock.DisplayFormula(WitnessFactorization()),
                    Paragraph(Text(
                        "Set D = 1000 and C = −539 + 496i. Write D^205 F((C+h)/D) = Σ a_k h^k, "
                        + "with Gaussian-integer coefficients. Put S = D^205. The O(205) analytic bounds "
                        + "use a linear pass over the coefficients after convolution. They give "
                        + "1000|a_0| ≤ 2537S, 5225S ≤ 1000|a_1| and "
                        + "1000 Σ_{k=2}^{205} 2^k |a_k| ≤ 425S, including both tail endpoints. "
                        + "The kernel checks the upper estimates with the coordinate sum norm and the "
                        + "lower estimate with the coordinate maximum norm. The comparison is strict because "
                        + "2537 + 425 < 5225 on the square boundary, where 1 ≤ |h| ≤ 2.")),
                    Paragraph(Text(
                        "The pinned rectangle zero-count theorem applies to the shifted polynomial and "
                        + "the linear function a_1 h, whose sole zero in the square is simple. "
                        + "For the resulting root z = (C+h)/D, the bound |C+500| < 498 gives "
                        + "|z+1/2| < (498+2)/1000 = 1/2. Thus z is nonzero and violates the inner bound.")),
                    Paragraph(Text(
                        "Jin, Ma and Wang, arXiv:2608.07898v2, repeat the translated annulus as Conjecture 5.1. "
                        + "Their Theorem 1.3 proves the separate origin-centered upper bound "
                        + "|z| ≤ 1 + (n−1)^(1/(n−1))."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brown-mol-2018-conjecture-4-2"), ResolutionKind.Refuted)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula P(Formula t, Formula z) => Call(new Formula.Subscript(F.Id("P"), t), z);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ForAllTyped(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ComplexNumbers => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula PolynomialFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), s = F.Id("S"), z = F.Id("z");
        Formula connected =
            new Formula.Relation(s, FormulaRelationOperator.MemberOf, Call(Named("ConnectedSubsets"), g));
        Formula sum = Seq(new Formula.Subscript(Sum, connected), Sp, Pow(z, new Formula.Absolute(s)));
        return Disp(ForAllTyped(v, Named("Type"),
            Seq(Forall, Sp, OpenBracket, Call(Named("Finite"), v), CloseBracket, Comma, Sp,
                ForAllTyped(g, Call(Named("SimpleGraph"), v), ForAllTyped(z, ComplexNumbers, Eq(P(g, z), sum))))));
    }

    private static Formula ClaimFormula()
    {
        Formula t = F.Id("T"), z = F.Id("z"), one = D(1);
        Formula n = Call(F.Id("n"), t);
        Formula m = Subtract(n, one);
        Formula distance = new Formula.Absolute(Add(z, Half));
        Formula bounds = new Formula.Logic(Le(Half, distance), FormulaLogicOperator.And,
            Le(distance, Add(Half, Pow(Parenthesized(m), new Formula.Fraction(one, m)))));
        Formula premises = new Formula.Logic(Le(D(2), n), FormulaLogicOperator.And, Eq(P(t, z), D(0)));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("T"), Named("FiniteTree"),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("z"), ComplexNumbers,
                new Formula.Logic(Parenthesized(premises), FormulaLogicOperator.Implies, Parenthesized(bounds)))));
    }

    private static Formula WitnessFactorization()
    {
        Formula z = F.Id("z");
        Formula leafChoices = Pow(Parenthesized(Add(D(1), z)), D(4));
        Formula rootChoices = Pow(Parenthesized(Add(D(1), Mul(z, leafChoices))), D(4, 1));
        Formula branchChoices = Mul(D(4, 1), Parenthesized(Add(D(4), leafChoices)));
        Formula factorization = Eq(P(F.Id("T"), z), Mul(z, Parenthesized(Add(rootChoices, branchChoices))));
        return Disp(ForAllTyped(z, ComplexNumbers, factorization));
    }
}
