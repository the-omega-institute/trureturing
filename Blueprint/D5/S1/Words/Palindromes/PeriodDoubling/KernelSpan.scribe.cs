using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class KernelSpanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix sums and triangular evaluations turn the automaticity target into a rank obstruction.", H("Rational Spans of Binary Kernels"), Blocks(
        Describe.Lean(DescribeId.Create("pd-kernelspan-twokernel"),
            DeclarationHandle.Create(Prefix + "twoKernel"), H("The literal binary kernel"),
            StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The binary kernel contains exactly the functions n mapped to f(2^e n+r), with e nonnegative and r strictly below 2^e. Its output carrier A is unrestricted."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-kernelspan-finite-difference-kernel-span"),
            DeclarationHandle.Create(Prefix + "finite_difference_kernel_span"), H("Finite differences give a finite prefix-sum span"),
            StatementSource.FromAuthor(FiniteFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational sequence starts at zero. Telescoping and splitting into complete residue blocks express every kernel sequence using the finite difference kernel and its prefix sums. A finite generating family therefore contains the entire rational kernel span."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("pd-kernelspan-triangular-evaluation-span-infinite"),
            DeclarationHandle.Create(Prefix + "triangular_evaluation_span_infinite"), H("Triangular evaluations force infinite dimension"),
            StatementSource.FromAuthor(TriangleFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Above the diagonal the evaluations are a_i+b_j, while the diagonal exceeds that value by one. After subtracting a and the constant b_j, evaluation induction proves linear independence. A finite-dimensional extension by two vectors cannot contain this infinite independent family."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula KernelFormula()
    {
        var sequence = Lam("n", N(), At(V("f"), Add(Mul(Pow(D(2), V("e")), V("n")), V("r"))));
        var address = Ex("e", N(), Ex("r", N(), And(LtF(V("r"), Pow(D(2), V("e"))),
            Eqn(V("g"), sequence))));
        var set = Seq(OpenBrace, V("g"), Colon, Fn(N(), V("A")), Sp, Mid, Sp, address, CloseBrace);
        return Disp(All("A", Ty("Type"), All("f", Fn(N(), V("A")),
            Eqn(Call("twoKernel", V("f")), set))));
    }
    private static Formula Span(Formula s) => Call("span", Q(), s);
    private static Formula FiniteFormula()
    {
        var difference = Lam("n", N(), Sub(At(V("P"), Add(V("n"), D(1))), At(V("P"), V("n"))));
        var conclusion = Call("FiniteDimensional", Q(), Span(Call("twoKernel", V("P"))));
        return Disp(All("P", Fn(N(), Q()), Imp(And(Eqn(At(V("P"), D(0)), D(0)),
            Call("Finite", Call("twoKernel", difference))), conclusion)));
    }
    private static Formula TriangleFormula()
    {
        var fj = At(V("f"), V("j"));
        var eval = At(fj, At(V("x"), V("i")));
        var sum = Add(At(V("a"), V("i")), At(V("b"), V("j")));
        var belongs = All("j", N(), Mem(fj, V("S")));
        var above = All("i", N(), All("j", N(), Imp(LtF(V("i"), V("j")), Eqn(eval, sum))));
        var diagonal = All("i", N(), Eqn(At(At(V("f"), V("i")), At(V("x"), V("i"))),
            Add(Add(At(V("a"), V("i")), At(V("b"), V("i"))), D(1))));
        return Disp(All("S", SetOf(Fn(N(), Q())), All("f", Fn(N(), Fn(N(), Q())),
            All("x", Fn(N(), N()), All("a", Fn(N(), Q()), All("b", Fn(N(), Q()),
                Imp(And(belongs, above, diagonal), NotF(Call("FiniteDimensional", Q(), Span(V("S")))))))))));
    }

}
