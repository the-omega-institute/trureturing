using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite avoidance formulas have the same signed correction term.",
        H("Finite Sums for the Arrow-Wilf Equivalence"),
        Blocks(
            Node("first-formula", "The first finite counting formula", "F1", F1Formula(),
                "F1 adds the n-th derangement number to the double sum indexed by 1 at most m at most n and 0 at most k at most n minus m, with factors choose(n minus m,k), choose(m plus k minus one,n minus m), and the k-th derangement number.", DescribeRole.Definition),
            Node("second-formula", "The second finite counting formula", "F2", F2Formula(),
                "F2 adds the n-th and (n minus one)-st derangement numbers to the double sum indexed by 1 at most m less than n and 0 at most r less than m, with factors choose(m minus one,r), choose(n minus m plus r minus one,r), r factorial, and the (m minus one minus r)-th derangement number.", DescribeRole.Definition),
            Node("reversed-hockey-stick", "The reversed hockey-stick identity", "reversed_hockey_stick", HockeyFormula(),
                "For i at most t and t plus two at most n, summing choose(n minus k minus two,t minus k) over k from i through t gives choose(n minus i minus one,t minus i).", DescribeRole.Theorem),
            Node("weighted-hockey-transform", "Weighted triangular-sum transform", "weighted_hockey_transform", null,
                "Over any commutative semiring, reversing the triangular sums against weights a(i) replaces the inner hockey-stick sum by choose(n minus i minus one,t minus i).", DescribeRole.Theorem),
            Node("common-signed-sum", "The common signed sum", "E", EFormula(),
                "E(n) is the integer double sum over zero at most t less than n and zero at most i at most t of minus one to the i times the ascending factorial from i plus one of length t minus i times choose(n minus i minus one,t minus i).", DescribeRole.Definition),
            Node("second-reindexing", "Reindexing the second correction", "f2_correction_reindexed", null,
                "The sum in F2 without its two derangement terms can be reindexed with t equal to m minus one and k equal to t minus r, producing a triangular sum over t and k.", DescribeRole.Theorem),
            Node("second-inner-transform", "Each inner sum becomes a signed inner sum", "f2_inner_eq_E_inner", null,
                "For t plus two at most n, the reindexed positive inner sum equals the t-th inner integer sum in E(n), after inclusion-exclusion and the weighted hockey-stick transform.", DescribeRole.Theorem),
            Node("second-correction", "The second correction equals E", "f2_correction_eq_E", CorrectionFormula(true),
                "For positive n, the (n minus one)-st derangement number plus the double-sum correction in F2 equals E(n). The derangement term supplies the missing boundary index t equal to n minus one.", DescribeRole.Theorem),
            Node("first-reindexing", "Reindexing the first correction", "f1_correction_reindexed", null,
                "The double sum in F1 can be reindexed by t equal to n minus m and k in the range zero through t; its coefficients become choose(n minus t plus k minus one,k) times choose(n minus t minus one,t minus k).", DescribeRole.Theorem),
            Node("positive-transform", "A positive finite transform", "positiveTransform", null,
                "The positive transform at p,t sums choose(p plus k,k) times choose(p,t minus k) times the k-th derangement number over k from zero through t.", DescribeRole.Definition),
            Node("positive-recurrence", "Recurrence for the positive transform", "positiveTransform_recurrence", null,
                "Multiplying the transform at p plus one,t plus one by p plus one gives the sum of p plus t plus two times the transform at p,t plus one and t plus one times the transform at p,t.", DescribeRole.Theorem),
            Node("signed-transform", "A signed finite transform", "signedTransform", null,
                "The signed transform at p,t sums minus one to the i times an ascending factorial and choose(p plus t minus i,t minus i) over i from zero through t.", DescribeRole.Definition),
            Node("signed-recurrence", "Recurrence for the signed transform", "signedTransform_recurrence", null,
                "The signed transform satisfies the same two-variable recurrence as the positive transform, with all terms interpreted as integers.", DescribeRole.Theorem),
            Node("transforms-equal", "Equality of the two finite transforms", "positiveTransform_eq_signedTransform", TransformEqualityFormula(),
                "For all natural p and t, the integer cast of the positive transform equals the signed transform.", DescribeRole.Theorem),
            Node("first-correction", "The first correction equals E", "f1_correction_eq_E", CorrectionFormula(false),
                "For every natural n, the double-sum correction in F1, cast to the integers, equals E(n) after reindexing and the finite transform identity.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula F1Formula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var k = F.Id("k");
        var term = Mul(Call("choose", Sub(n, m), k),
            Call("choose", Sub(Add(m, k), D(1)), Sub(n, m)), Call("numDerangements", k));
        return Disp(All("n", Eq(Call("F1", n),
            Add(Call("numDerangements", n),
                SumOver("m", Call("Icc", D(1), n),
                    SumOver("k", Call("range", Add(Sub(n, m), D(1))), term))))));
    }

    private static Formula F2Formula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var r = F.Id("r");
        var term = Mul(Call("choose", Sub(m, D(1)), r),
            Call("choose", Sub(Add(Sub(n, m), r), D(1)), r), Call("factorial", r),
            Call("numDerangements", Sub(Sub(m, D(1)), r)));
        return Disp(All("n", Eq(Call("F2", n),
            Add(Call("numDerangements", n), Call("numDerangements", Sub(n, D(1))),
                SumOver("m", Call("Icc", D(1), Sub(n, D(1))),
                    SumOver("r", Call("range", m), term))))));
    }

    private static Formula EFormula()
    {
        var n = F.Id("n"); var t = F.Id("t"); var i = F.Id("i");
        var term = Mul(new Formula.Power(new Formula.Negate(D(1)), i),
            Call("ascFactorial", Add(i, D(1)), Sub(t, i)),
            Call("choose", Sub(Sub(n, i), D(1)), Sub(t, i)));
        return Disp(All("n", Eq(Call("E", n),
            SumOver("t", Call("range", n),
                SumOver("i", Call("range", Add(t, D(1))), term)))));
    }

    private static Formula HockeyFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var t = F.Id("t"); var k = F.Id("k");
        var left = SumOver("k", Call("Icc", i, t),
            Call("choose", Sub(Sub(n, k), D(2)), Sub(t, k)));
        var right = Call("choose", Sub(Sub(n, i), D(1)), Sub(t, i));
        return Disp(All("n", All("i", All("t", Imp(
            And(Le(i, t), Le(Add(t, D(2)), n)), Eq(left, right))))));
    }

    private static Formula CorrectionFormula(bool second)
    {
        var n = F.Id("n"); var m = F.Id("m");
        Formula left;
        if (second)
        {
            var r = F.Id("r");
            var term = Mul(Call("choose", Sub(m, D(1)), r),
                Call("choose", Sub(Add(Sub(n, m), r), D(1)), r),
                Call("factorial", r), Call("numDerangements", Sub(Sub(m, D(1)), r)));
            left = Add(AsInt(Call("numDerangements", Sub(n, D(1)))),
                AsInt(SumOver("m", Call("Icc", D(1), Sub(n, D(1))),
                    SumOver("r", Call("range", m), term))));
        }
        else
        {
            var k = F.Id("k");
            var term = Mul(Call("choose", Sub(n, m), k),
                Call("choose", Sub(Add(m, k), D(1)), Sub(n, m)),
                Call("numDerangements", k));
            left = AsInt(SumOver("m", Call("Icc", D(1), n),
                SumOver("k", Call("range", Add(Sub(n, m), D(1))), term)));
        }
        var equality = Eq(left, Call("E", n));
        return Disp(All("n", second ? Imp(Le(D(1), n), equality) : equality));
    }

    private static Formula TransformEqualityFormula()
    {
        var p = F.Id("p"); var t = F.Id("t");
        return Disp(All("p", All("t", Eq(AsInt(Call("positiveTransform", p, t)),
            Call("signedTransform", p, t)))));
    }

    private static Formula AsInt(Formula value) =>
        Seq(Open, value, Colon, Sp, new Formula.Integers(), Close);

    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(variable), InMacro, Sp, domain), Sp, Open, body, Close);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(params Formula[] args) => Fold(args, FormulaBinaryOperator.Add);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(params Formula[] args) => Fold(args, FormulaBinaryOperator.Multiply);
    private static Formula Fold(Formula[] args, FormulaBinaryOperator op)
    {
        Formula result = args[0];
        for (var i = 1; i < args.Length; i++) result = new Formula.Binary(result, op, args[i]);
        return result;
    }
}
