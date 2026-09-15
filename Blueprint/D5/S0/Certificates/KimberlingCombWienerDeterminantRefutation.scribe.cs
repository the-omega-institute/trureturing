using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KimberlingCombWienerDeterminantRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kimberling2012a192023");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At n = 3, the printed comb Wiener-index and determinant-count conjecture fails.",
        H("The OEIS A192023 Comb Wiener-Index Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a192023-comb"),
                DeclarationHandle.Create(Prefix + "comb"),
                H("The comb-shaped graph"),
                StatementSource.FromAuthor(CombFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vertices are Fin m on the spine and a second copy Fin m of "
                        + "pendant vertices. The fromRel relation joins spine index i to "
                        + "spine index j when i.val + 1 = j.val and joins spine i to "
                        + "pendant j when i = j. fromRel adds reverse edges and excludes loops."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a192023-wiener-index"),
                DeclarationHandle.Create(Prefix + "wienerIndex"),
                H("The Wiener index"),
                StatementSource.FromAuthor(WienerFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite vertex type V with decidable equality, the filter removes "
                        + "diagonal pairs from the symmetric square Sym2 V. Each remaining "
                        + "unordered pair occurs once; Sym2.lift evaluates its graph distance, "
                        + "using dist_comm for independence of the order of endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a192023-matrix-count"),
                DeclarationHandle.Create(Prefix + "matrixCount"),
                H("Determinant-constrained matrix count"),
                StatementSource.FromAuthor(MatrixFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The nested finite Cartesian product has row-major coordinates "
                        + "q = (a,(b,(c,d))) and denotes the matrix [[a,b],[c,d]]. "
                        + "Matrix.det_fin_two is the row-major formula a*d-b*c. The integer "
                        + "interval Icc(1, n) taken four times contains 1 through n; the filter requires "
                        + "determinant 2n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a192023-printed-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The printed matrix-count conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n greater than two, A192023(n-2) denotes the "
                        + "Wiener index of the comb on 2(n-2) vertices, not an assumed "
                        + "evaluation of its closed formula. The comparison counts "
                        + "exactly the matrices in the printed comment."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a192023-printed-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The printed conjecture fails at n = 3"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The comb with two vertices is a single edge, so its only unordered "
                        + "pair contributes distance one. For n = 3, entries in {1,2,3} "
                        + "and ad-bc = 6 force a = d = 3 and bc = 3. Exactly the "
                        + "matrices [[3,1],[3,3]] and [[3,3],[1,3]] qualify, giving "
                        + "count two. One differs from two. This refutes only the printed "
                        + "comment and asserts no corrected statement."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a192023-comb-wiener-determinant-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula CombFormula()
    {
        var m = F.Id("m");
        var u = F.Id("u");
        var i = F.Id("i");
        var j = F.Id("j");
        var inner = QualifiedCall("Sum", "elim",
            Lam(j, Equal(Add(Field(i, "val"), D(1)), Field(j, "val"))),
            Lam(j, Equal(i, j)));
        var outer = QualifiedCall("Sum", "elim", Lam(i, inner),
            Lam(Underscore, Lam(Underscore, F.Id("False"))), u);
        var vertex = Call("Sum", Call("Fin", m), Call("Fin", m));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, m, Colon, Sp, Naturals(), Comma),
            Seq(Call("comb", m), Colon, Sp, Call("SimpleGraph", vertex), Sp, Eq, Sp,
                QualifiedCall("SimpleGraph", "fromRel", Lam(u, outer))),
        ]));
    }

    private static Formula WienerFormula()
    {
        var v = F.Id("V");
        var g = F.Id("G");
        var p = F.Id("p");
        var u = F.Id("u");
        var w = F.Id("v");
        var sym2 = Call("Sym2", v);
        var univ = Seq(Qualified("Finset", "univ"), Colon, Sp, Call("Finset", sym2));
        var filtered = Apply(Field(Parenthesized(univ), "filter"),
            Lam(p, new Formula.Not(Field(p, "IsDiag"))));
        var commutativity = Apply(
            Field(g, Snake("dist", "comm")),
            NamedArgument("u", u),
            NamedArgument("v", w));
        var lift = QualifiedCall("Sym2", "lift",
            Seq(Langle, Sp, Field(g, "dist"), Comma, Sp,
                LamMany([u, w], commutativity), Sp, Rangle), p);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, OpenBrace, v, Colon, Sp, F.Id("Type"), Star, CloseBrace,
                Sp, OpenBracket, Call("Fintype", v), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", v), CloseBracket, Comma),
            Seq(Forall, Sp, g, Colon, Sp, Call("SimpleGraph", v), Comma),
            Seq(Call("wienerIndex", g), Colon, Sp, Naturals(), Sp, Eq, Sp,
                new Formula.Subscript(Sum, Seq(p, Sp, InMacro, Sp, filtered)), Sp, lift),
        ]));
    }

    private static Formula MatrixFormula()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        var product = FinsetProduct(
            QualifiedCall("Finset", "Icc", Coerce(D(1), Integers()), Coerce(n, Integers())),
            FinsetProduct(
                QualifiedCall("Finset", "Icc", Coerce(D(1), Integers()), Coerce(n, Integers())),
                FinsetProduct(
                    QualifiedCall("Finset", "Icc", Coerce(D(1), Integers()), Coerce(n, Integers())),
                    QualifiedCall("Finset", "Icc", Coerce(D(1), Integers()), Coerce(n, Integers())))));
        var ad = Multiply(Project(q, 1), Project(q, 2, 2, 2));
        var bc = Multiply(Project(q, 2, 1), Project(q, 2, 2, 1));
        var condition = Equal(Subtract(ad, bc),
            Multiply(D(2), Coerce(n, Integers())));
        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            new Formula.Relation(
                Seq(Call("matrixCount", n), Colon, Sp, Naturals()),
                FormulaRelationOperator.Equal,
                QualifiedCall("Finset", "card",
                    QualifiedCall("Finset", "filter", product, Lam(q, condition))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        return Disp(new Formula.Logic(Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("n"), Naturals(),
                new Formula.Logic(
                    new Formula.Relation(D(2), FormulaRelationOperator.LessThan, n),
                    FormulaLogicOperator.Implies,
                    new Formula.Relation(
                        Call("wienerIndex", Call("comb", Subtract(n, D(2)))),
                        FormulaRelationOperator.Equal, Call("matrixCount", n)))))));
    }

    private static Formula Lam(Formula variable, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body));

    private static Formula LamMany(Formula[] variables, Formula body)
    {
        var items = new List<Formula> { LambdaLower, Sp };
        for (var index = 0; index < variables.Length; index++)
        {
            if (index > 0) items.Add(Sp);
            items.Add(variables[index]);
        }
        items.AddRange([Sp, Mapsto, Sp, body]);
        return Parenthesized(Seq([.. items]));
    }

    private static Formula Qualified(string prefix, string name) =>
        Seq(F.Id(prefix), Dot, F.Id(name));

    private static Formula QualifiedCall(string prefix, string name, params Formula[] args) =>
        Apply(Qualified(prefix, name), args);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Field(Formula value, string name) =>
        Seq(value, Dot, F.Id(name));

    private static Formula Field(Formula value, Formula name) =>
        Seq(value, Dot, name);

    private static Formula Project(Formula value, params byte[] fields)
    {
        var result = value;
        foreach (var field in fields)
        {
            result = Seq(result, Dot, D(field));
        }
        return result;
    }

    private static Formula NamedArgument(string name, Formula value) =>
        Parenthesized(Seq(F.Id(name), Sp, Colon, Eq, Sp, value));

    private static Formula Snake(string first, string second) =>
        new Formula.Subscript(F.Id(first), F.Id(second));

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula FinsetProduct(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, new Formula.Power(Times, F.Id("s")), Sp, right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Integers() => new Formula.Integers();

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
