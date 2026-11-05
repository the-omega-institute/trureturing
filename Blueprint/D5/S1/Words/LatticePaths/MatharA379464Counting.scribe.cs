using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.LatticePaths;

internal sealed class MatharA379464CountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/LatticePaths/MatharA379464Counting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathar2025a379464");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal path counting and optional-letter insertion for OEIS A379464.",
        H("A379464 path counting"),
        Blocks(
            Paragraph(Text("The unpaginated OEIS A379464 Name field states: “a(n) is the total number of paths starting at (0, 0), ending at (n, 0), consisting of steps (1, 1), (1, 0), (1, -3), and staying on or above y = -2.” The vertical increments are 1, 0, and -3; the empty path is included. Removing zero increments gives a zero-free word; inserting optional letters is counted by a binomial transform.")),
            Node("Step", "The three vertical increments", StepFormula(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("IsPath", "The bounded path predicate", IsPathFormula(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("a", "The path count", AFormula(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("three_positive_rotations", "Three positive cyclic rotations", ThreeRotationsFormula(), AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("binomial_counting", "The optional-letter count", BinomialFormula(), AssessedProvenance.FromLiterature(Source), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mathar379464-counting-" + name.ToLowerInvariant().Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("The displayed formula records the finite-word counting statement and its coefficient identity."))), role);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Step() => Call("Step");
    private static Formula A(Formula n) => Call("a", n);
    private static Formula P(Formula w) => Call("IsPath", w);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Par(Formula f) => Parenthesized(f);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Cast(Formula x, Formula type) => Par(Seq(x, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Par(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Sum(Formula index, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, type)), Sp, body);
    private static Formula SetOfSteps() => Qualified("Finset", "insert", D(1), Qualified("Finset", "insert", D(0), Qualified("Finset", "singleton", new Formula.Negate(Num(3)))));
    private static Formula Length(Formula w) => Qualified("List", "length", w);
    private static Formula RotatedPrefix(Formula w, Formula j, Formula r) =>
        Qualified("List", "sum", Qualified("List", "take", r, Qualified("List", "rotate", w, Qualified("Fin", "val", j))));

    private static Formula StepFormula()
    {
        Formula s = F.Id("s");
        Formula predicate = Lambda("s", Z(), Mem(s, SetOfSteps()));
        return Disp(Eq(Step(), Call("Subtype", predicate)));
    }

    private static Formula IsPathFormula()
    {
        var n = F.Id("n"); var w = F.Id("w"); var i = F.Id("i"); var r = F.Id("r");
        Formula wi = Qualified("Subtype", "val", Call("w", i));
        Formula total = Sum(i, Fin(n), wi);
        Formula prefixTerm = Call("ite", Lt(Qualified("Fin", "val", i), r), wi, D(0));
        Formula prefix = Sum(i, Fin(n), prefixTerm);
        Formula body = And(Eq(total, D(0)), All("r", N(), Imp(Le(r, n), Le(Par(Seq(Minus, D(2))), prefix))));
        return Disp(All("n", N(), All("w", new Formula.TypeArrow(Fin(n), Step()), Eq(P(w), body))));
    }

    private static Formula AFormula()
    {
        var n = F.Id("n"); var w = F.Id("w");
        Formula type = new Formula.TypeArrow(Fin(n), Step());
        Formula carrier = Call("Subtype", Lambda("w", type, P(w)));
        return Disp(All("n", N(), Eq(A(n), Cast(Qualified("Fintype", "card", carrier), Z()))));
    }

    private static Formula ThreeRotationsFormula()
    {
        var w = F.Id("w"); var x = F.Id("x"); var j = F.Id("j"); var r = F.Id("r");
        Formula positive = All("r", N(), Imp(Lt(D(0), r), Imp(Le(r, Length(w)), Lt(D(0), RotatedPrefix(w, j, r)))));
        Formula cuts = Call("Subtype", Lambda("j", Fin(Length(w)), positive));
        Formula stepBound = All("x", Z(), Imp(Mem(x, w), Le(x, D(1))));
        return Disp(All("w", Call("List", Z()), Imp(stepBound,
            Imp(Eq(Qualified("List", "sum", w), D(3)), Eq(Qualified("Fintype", "card", cuts), D(3))))));
    }

    private static Formula BinomialFormula()
    {
        var n = F.Id("n"); var k = F.Id("k");
        Formula choose = Cast(Qualified("Nat", "choose", n, Mul(D(4), k)), Q());
        Formula numerator = Mul(D(3), Cast(Qualified("Nat", "factorial", Add(Mul(D(4), k), D(2))), Q()));
        Formula denominator = Mul(Cast(Qualified("Nat", "factorial", k), Q()), Cast(Qualified("Nat", "factorial", Add(Mul(D(3), k), D(3))), Q()));
        Formula ratio = new Formula.Fraction(numerator, denominator);
        Formula summand = Mul(choose, ratio);
        Formula sum = Sum(k, Qualified("Finset", "range", Add(n, D(1))), summand);
        return Disp(All("n", N(), Eq(Cast(A(n), Q()), sum)));
    }
}
