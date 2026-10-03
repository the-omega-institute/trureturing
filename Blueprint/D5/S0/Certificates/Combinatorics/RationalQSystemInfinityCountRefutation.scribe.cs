using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class RationalQSystemInfinityCountRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hou2024rationalqsystems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hou--Jiang--Miao's root-of-unity primitive-count formula is negative at the admissible triple (26,11,1), so it cannot be a natural-number count.",
        H("Refutation of the rational Q-system infinite-root count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hou-jiang-miao-formula"),
                DeclarationHandle.Create(Prefix + "formula"),
                H("The proposed primitive-count expression"),
                StatementSource.FromAuthor(Disp(FormulaDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Appendix C, equation (C.2), page 35: \"N^{pri}_{±∞}(L, M, n_±) = "
                        + "\\binom{L}{M − n_±} − \\sum_{x=0}^{M−n_±−1} \\binom{L}{x}, (C.2)\". "
                        + "The Lean formula uses Int subtraction after casting each binomial "
                        + "coefficient; Finset.range(M − n) enumerates x = 0 through M − n − 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hou-jiang-miao-admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("The admissible root-of-unity scope"),
                StatementSource.FromAuthor(Disp(AdmissibleDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source says: \"We focus on the case with no twist, i.e. κ = 1 and "
                        + "η = iπ/3 for simplicity.\" It then considers even L and primitive "
                        + "states with M ≤ L/2. Equations (3.15)--(3.17) give 0 ≤ n ≤ 2 and, "
                        + "for κ = 1 and ℓ₂ = 3, L ≡ 2(M − n) (mod 6). The displayed predicate "
                        + "also records n ≥ 1 and n ≤ M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hou-jiang-miao-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The natural-valued count claim"),
                StatementSource.FromAuthor(Disp(ClaimDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Appendix C, equation (C.2), page 35 states verbatim: \"Before introducing "
                        + "the algorithm, we make the following conjecture for the number of "
                        + "primitive states with infinite Bethe root(s) by observing the numerical "
                        + "results: N^{pri}_{±∞}(L, M, n_±) = \\binom{L}{M − n_±} − "
                        + "\\sum_{x=0}^{M−n_±−1} \\binom{L}{x}, (C.2), when n_± = n_+ = n_− is "
                        + "a solution to (3.15). When there is no solution to (3.15), "
                        + "N^{pri}_{±∞}(L, M, n_±) = 0.\" A count of primitive states is a "
                        + "natural number, so (C.2) implies this existential natural-valued "
                        + "claim for the true count."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hou-jiang-miao-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture is refuted"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At (L, M, n) = (26, 11, 1), all admissibility clauses hold and the "
                        + "formula evaluates to −346802: binom(26,10) = 5,311,735 while "
                        + "the sum through x = 9 is 5,658,537. A natural-number cast to ℤ "
                        + "is nonnegative, so the displayed negative value contradicts the "
                        + "claim. This refutes (C.2) without modelling Bethe states."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hou-jiang-miao-2023-root-of-unity-infinity-count-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static Formula FormulaDefinition()
    {
        Formula l = F.Id("L"), m = F.Id("M"), n = F.Id("n"), x = F.Id("x");
        Formula choose(Formula top, Formula bottom) => Qualified("Nat", "choose", top, bottom);
        Formula term = Cast(choose(l, Sub(m, n)), Integers());
        Formula summand = Cast(choose(l, x), Integers());
        Formula sum = new Formula.Subscript(
            Sum,
            Seq(x, Sp, InMacro, Sp, Qualified("Finset", "range", Sub(m, n))));
        Formula body = Eq(Call("formula", l, m, n), Seq(term, Sp, Minus, Sp, sum, Sp, summand));
        return All("L", Naturals(), All("M", Naturals(), All("n", Naturals(), body)));
    }

    private static Formula AdmissibleDefinition()
    {
        Formula l = F.Id("L"), m = F.Id("M"), n = F.Id("n");
        Formula left = Call("Admissible", l, m, n);
        Formula lz = Cast(l, Integers());
        Formula mz = Cast(m, Integers());
        Formula nz = Cast(n, Integers());
        Formula clauses = And(
            Call("Even", l),
            And(Le(D(1), m),
                And(Le(Mul(D(2), m), l),
                    And(Le(D(1), n),
                        And(Le(n, D(2)),
                            And(Le(n, m), Congruent(lz, Mul(D(2), IntSub(mz, nz)), D(6))))))));
        return All("L", Naturals(), All("M", Naturals(), All("n", Naturals(), Iff(left, clauses))));
    }

    private static Formula ClaimDefinition()
    {
        Formula l = F.Id("L"), m = F.Id("M"), n = F.Id("n"), count = F.Id("N");
        Formula countType = Arrow(Naturals(), Arrow(Naturals(), Arrow(Naturals(), Naturals())));
        Formula equation = Eq(
            Cast(Apply(count, l, m, n), Integers()),
            Call("formula", l, m, n));
        Formula quantified = Exists("N", countType,
            All("L", Naturals(), All("M", Naturals(), All("n", Naturals(),
                Implies(Call("Admissible", l, m, n), equation)))));
        return Iff(F.Id("claim"), quantified);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Named(owner), Dot, Named(name)), [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(left, Sp, Equiv, Sp, right, Sp, Parenthesized(Seq(Operatorname, Grp(F.Id("mod")), Sp, modulus)));
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula IntSub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
