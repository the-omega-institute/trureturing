using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeightedLegalPathTemperleyLiebDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite symmetric weighted legal paths carry the exact local Temperley-Lieb projections.",
        H("Weighted Legal-Path Temperley-Lieb Relations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-legal-path-temperley-lieb"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb."
                        + "weighted_legal_path_temperley_lieb"),
                H("Weighted path projections satisfy all four local relations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let L be any finite label type and R a symmetric Boolean adjacency "
                            + "relation, including possible self-loops. Every label has a "
                            + "strictly positive real weight d, delta is strictly positive, "
                            + "and the sum of d(b) over R(a,b) equals delta times d(a) "
                            + "for every a. Fix any path length n and endpoints s,t. "
                            + "The path basis contains precisely the legal length-n paths "
                            + "from s to t and may be empty.")),
                    Paragraph(Text(
                        "For every interior i, P_i(x,y) is zero unless x and y agree "
                            + "outside i and x at i-1 equals x at i+1. In the remaining "
                            + "case its literal FT.12 coefficient is the complex cast of "
                            + "sqrt(d(x_i) * d(y_i)) / (delta * d(x_(i-1))). "
                            + "This is the source's square root of the product, with no "
                            + "rescaling or normalization of P_i.")),
                    Paragraph(Text(
                        "The theorem establishes self-adjointness and idempotence at every "
                            + "interior index, the forward adjacent triple product whenever "
                            + "i+1 is interior, and commutation for both ordered cases of "
                            + "distance at least two. Its local replacement equivalence "
                            + "identifies a legal fiber with the neighbors of its common "
                            + "flank; the proof also establishes the adjacent unique "
                            + "survivor and the distant locality argument. No nonempty "
                            + "path-space premise is used."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var nameParts = name.Split('.');
        var operatorParts = new List<Formula> { F.Id(nameParts[0]) };
        for (var part = 1; part < nameParts.Length; part++)
        {
            operatorParts.Add(Dot);
            operatorParts.Add(F.Id(nameParts[part]));
        }

        var items = new List<Formula> { Operatorname, Grp([.. operatorParts]), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula At(Formula function, Formula index) => Apply(function, index);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var index = terms.Length - 2; index >= 0; index--)
            result = new Formula.Logic(terms[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula labels = F.Id("L");
        Formula relation = F.Id("R");
        Formula weights = F.Id("d");
        Formula delta = Delta;
        Formula length = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula p = F.Id("P");
        Formula pi = Sub(p, i);
        Formula pj = Sub(p, j);
        Formula next = Sub(p, Seq(i, Plus, D(1)));
        Formula interior = Seq(D(1), Le, Sp, i, Lt, length);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula k = F.Id("k");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula path = Call("LegalPath", relation, length, F.Id("s"), F.Id("t"));
        Formula pathFunctionType = new Formula.TypeArrow(
            Call("Fin", Seq(length, Plus, D(1))), labels);
        Formula pathAdjacency = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Call("Fin", length),
            Apply(relation,
                At(x, k),
                At(x, Seq(k, Plus, D(1)))));
        Formula pathBody = And(
            Equal(At(x, D(0)), F.Id("s")),
            Equal(At(x, length), F.Id("t")),
            pathAdjacency);
        Formula pathDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, path, Colon, Sp, F.Id("Type"),
            Sp, Eq, Sp, OpenBrace, x, Colon, Sp, pathFunctionType, Sp, Bar, Sp,
            pathBody, CloseBrace, Semi, Sp);
        Formula support = And(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("k"),
                Call("Fin", Seq(length, Plus, D(1))),
                Implies(
                    NotEqual(k, i),
                    Equal(At(x, k), At(y, k)))),
            Equal(
                At(x, Seq(i, Minus, D(1))),
                At(x, Seq(i, Plus, D(1)))));
        Formula coefficient = Call(
            "Complex.ofReal",
            new Formula.Fraction(
                Seq(Sqrt, Grp(new Formula.Binary(
                    At(weights, At(x, i)),
                    FormulaBinaryOperator.Multiply,
                    At(weights, At(y, i))))),
                new Formula.Binary(
                    delta,
                    FormulaBinaryOperator.Multiply,
                    At(weights, At(x, Seq(i, Minus, D(1)))))));
        Formula piecewise = Seq(
            Open, Begin, Grp(F.Id("cases")),
            coefficient, Sp, Amp, Sp, F.Text, Grp(F.Id("if")), Sp, Open, support, Close,
            RowBreak,
            D(0), Sp, Amp, Sp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")), Close);
        Formula projectionDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, pi, Colon, Sp,
            Call("Matrix", path, path, complex), Comma, Sp,
            i, InMacro, Sp, natural, Comma, Sp, interior, Comma, Sp,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [
                    new Formula.BoundVariable(FormulaIdentifier.Create("x"), path),
                    new Formula.BoundVariable(FormulaIdentifier.Create("y"), path),
                ],
                Equal(Apply(pi, x, y), piecewise)),
            Semi, Sp);
        Formula pf = Seq(
            Forall, Sp, a, InMacro, Sp, labels, Comma, Sp,
            D(0), Lt, Sub(weights, a), Sp, Land, Sp,
            Sum, Underscore, Grp(b, Colon, Sp, Call("R", a, b)), Sp,
            Sub(weights, b), Eq, delta, Sp, Sub(weights, a));
        Formula adjacent = Seq(D(1), Le, Sp, i, Comma, Sp, i, Plus, D(1), Lt, length);
        Formula distant = Seq(
            D(1), Le, Sp, i, Lt, length, Comma, Sp,
            D(1), Le, Sp, j, Lt, length, Comma, Sp,
            i, Plus, D(2), Le, Sp, j, Sp, Lor, Sp, j, Plus, D(2), Le, Sp, i);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, labels, Colon, Sp, Operatorname, Grp(F.Id("Finite")), Comma, Sp,
            relation, Colon, Sp, labels, Sp, To, Sp, labels, Sp, To, Sp,
            Operatorname, Grp(F.Id("Prop")), Comma, Esc,
            Call("Symmetric", relation), Comma, Sp,
            weights, Colon, Sp, labels, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Lt, delta, Comma, Sp, pf, Comma, Esc,
            Forall, Sp, length, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            F.Id("s"), Comma, Sp, F.Id("t"), InMacro, Sp, labels, Comma, RowBreak,
            pathDefinition, RowBreak,
            projectionDefinition, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, interior, Sp, Rightarrow, Sp,
            Call("conjTranspose", pi), Eq, pi, Sp, Land, Sp, pi, pi, Eq, pi, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, adjacent, Sp, Rightarrow, Sp,
            pi, next, pi, Eq, delta, Caret, Grp(Minus, D(2)), pi, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp, distant, Sp, Rightarrow, Sp,
            pi, pj, Eq, pj, pi, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
