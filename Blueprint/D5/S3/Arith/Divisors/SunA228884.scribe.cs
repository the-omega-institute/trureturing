using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class SunA228884Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Divisors/SunA228884";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/sun2013oeisa228884");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime divisors of composite gcd determinants are smaller than the index.",
        H("Zhi-Wei Sun's OEIS A228884 composite gcd-determinant bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sun-a228884-matrix"),
                DeclarationHandle.Create(Module + ".C"),
                H("The gcd-entry matrix"),
                StatementSource.FromAuthor(CFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A228884 NAME, page not numbered: “Determinant of the n X n matrix "
                        + "with (i,j)-entry equal to the greatest common divisor of i-j and n.” "
                        + "The source program is “a[n_]:=Det[Table[GCD[i-j,n],{i,1,n},{j,1,n}]]”. "
                        + "The Lean expression uses Fin n "
                        + "labels, adds one to each label, performs integer subtraction, and "
                        + "applies Int.gcd before casting the result to the matrix entry type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sun-a228884-determinant"),
                DeclarationHandle.Create(Module + ".D"),
                H("The determinant sequence"),
                StatementSource.FromAuthor(DFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A228884 NAME, page not numbered: “Determinant of the n X n matrix "
                        + "with (i,j)-entry equal to the greatest common divisor of i-j and n.” "
                        + "D n is Matrix.det of C n, including the empty determinant at n=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sun-a228884-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The composite-index prime-divisor conjecture"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A228884 COMMENTS clause (ii), page not numbered: “(ii) For any composite "
                        + "number n, all prime divisors of a(n) are smaller than n.” The source "
                        + "definition is encoded with n ≥ 4, ¬Nat.Prime n, integer divisibility "
                        + "of D n by the natural prime q, and q < n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sun-a228884-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The prime-divisor bound holds"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "CRT reindexing gives D(uv)=D(u)^v D(v)^u for coprime positive u and v. "
                            + "The gcd Fourier transform factors over prime powers, and its local "
                            + "eigenvalue products at exponent at least two have prime divisors below the local order. "
                            + "Exponent-one factors are bounded by 2p-1 and the remaining cofactor "
                            + "in a composite index supplies 2p ≤ n.")),
                    Paragraph(Text(
                        "The proof therefore establishes the complete statement for every n ≥ 4 "
                            + "with ¬Nat.Prime n. Positivity and the separate divisibility clause "
                            + "of the OEIS entry are not asserted here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sun228884"),
                    ResolutionKind.Proved)))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Call(Formula qualified, params Formula[] arguments) =>
        new Formula.Apply(qualified, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));

    private static Formula CFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var iVal = Call("val", i);
        var jVal = Call("val", j);
        var entry = Call(Qualified("Int", "gcd"),
            Sub(Parenthesized(Add(Typed(iVal, Z()), D(1))),
                Parenthesized(Add(Typed(jVal, Z()), D(1)))), Typed(n, Z()));
        return Disp(All("n", N(), All("i", Fin(n), All("j", Fin(n),
            Eq(new Formula.Apply(Call("C", n), [i, j]), Typed(entry, Z()))))));
    }

    private static Formula DFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", N(), Eq(Call("D", n), Call(Qualified("Matrix", "det"), Call("C", n)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        return All("n", N(), Implies(Le(D(4), n),
            Implies(Not(Call(Qualified("Nat", "Prime"), n)),
                All("q", N(), Implies(Call(Qualified("Nat", "Prime"), q),
                    Implies(new Formula.Relation(Typed(q, Z()), FormulaRelationOperator.Divides,
                        Call("D", n)), Lt(q, n)))))));
    }
}
