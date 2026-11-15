using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class GoldenArcFirstReturnCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fractional phases add their forward displacement when the sum stays below one.",
        H("Forward displacement without wrapping"),
        Blocks(Describe.Lean(DescribeId.Create("cassaigne-owner-orbitphase"), DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.orbitPhase"), H("orbitPhase"), StatementSource.FromAuthor(Disp(All(Q("alpha"), Q("Real"), All(Q("i"), Q("Nat"), Seq(Q("orbitPhase"), Sp, Q("alpha"), Sp, Q("i"), Sp, Eq, Sp, Parenthesized(Seq(Q("Int.fract"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Q("i"), Sp, Plus, Sp, D(1), Sp, Colon, Sp, Q("Nat"))), Sp, Colon, Sp, Q("Real"))), Sp, Cdot, Sp, Q("alpha")))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("cassaigne-owner-irrational-nat-mul-fract-ne-zero"), DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.irrational_nat_mul_fract_ne_zero"), H("irrational nat mul fract ne zero"), StatementSource.FromAuthor(Disp(All(Q("alpha"), Q("Real"), Seq(Parenthesized(Seq(Q("Irrational"), Sp, Q("alpha"))), Rightarrow, All(Q("k"), Q("Nat"), Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Q("k"))), Rightarrow, Seq(Q("Int.fract"), Sp, Parenthesized(Seq(Parenthesized(Seq(Q("k"), Sp, Colon, Sp, Q("Real"))), Sp, Cdot, Sp, Q("alpha"))), Sp, Neq, Sp, D(0)))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("cassaigne-owner-exists-orbit-phase-mem-ioo"), DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.exists_orbit_phase_mem_Ioo"), H("exists orbit phase mem Ioo"), StatementSource.FromAuthor(Disp(All(Q("alpha"), Q("Real"), All(Q("a"), Q("Real"), All(Q("b"), Q("Real"), Seq(Parenthesized(Seq(Q("Irrational"), Sp, Q("alpha"))), Rightarrow, Seq(Parenthesized(Seq(D(0), Sp, Leq, Sp, Q("a"))), Rightarrow, Seq(Parenthesized(Seq(Q("a"), Sp, Lt, Sp, Q("b"))), Rightarrow, Seq(Parenthesized(Seq(Q("b"), Sp, Leq, Sp, D(1))), Rightarrow, Seq(Exists, Sp, Q("i"), Sp, Comma, Sp, Q("orbitPhase"), Sp, Q("alpha"), Sp, Q("i"), Sp, InMacro, Sp, Q("Ioo"), Sp, Q("a"), Sp, Q("b"))))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("cassaigne-owner-fract-add-displacement-of-wrap"), DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_wrap"), H("fract add displacement of wrap"), StatementSource.FromAuthor(Disp(All(Q("alpha"), Q("Real"), All(Q("x"), Q("Real"), Seq(Parenthesized(Seq(Q("Irrational"), Sp, Q("alpha"))), Rightarrow, All(Q("k"), Q("Nat"), Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Q("k"))), Rightarrow, Seq(Parenthesized(Seq(Q("x"), Sp, Lt, Sp, D(1))), Rightarrow, Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, Q("x"), Sp, Plus, Sp, Q("forwardDisplacement"), Sp, Q("alpha"), Sp, Q("k"))), Rightarrow, Seq(Q("Int.fract"), Sp, Parenthesized(Seq(Q("x"), Sp, Plus, Sp, Parenthesized(Seq(Q("k"), Sp, Colon, Sp, Q("Real"))), Sp, Cdot, Sp, Q("alpha"))), Sp, Eq, Sp, Q("x"), Sp, Minus, Sp, Q("backwardDisplacement"), Sp, Q("alpha"), Sp, Q("k"))))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains."))), DescribeRole.Theorem),
Describe.Lean(
            DescribeId.Create("fract-add-displacement-of-no-wrap"),
            DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap"),
            H("Fractional addition without wrapping"),
            StatementSource.FromAuthor(NoWrapFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For real alpha and x and a natural k, if x is nonnegative and x plus forwardDisplacement alpha k is less than one, the fractional part of x plus k times alpha equals that sum."))),
            DescribeRole.Theorem)), []));

    private static Formula NoWrapFormula()
    {
        var alpha = F.Id("alpha");
        var x = F.Id("x");
        var k = F.Id("k");
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var displacement = Call("forwardDisplacement", alpha, k);
        var sum = new Formula.Binary(x, FormulaBinaryOperator.Add, displacement);
        var cast = Parenthesized(Seq(Dotted("Nat", "cast", k), Sp, Colon, Sp, real));
        var product = new Formula.Binary(cast, FormulaBinaryOperator.Multiply, alpha);
        var argument = new Formula.Binary(x, FormulaBinaryOperator.Add, product);
        var conclusion = new Formula.Relation(Dotted("Int", "fract", argument),
            FormulaRelationOperator.Equal, sum);
        var nonnegative = new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, x);
        var nowrap = new Formula.Relation(sum, FormulaRelationOperator.LessThan, D(1));
        return Disp(Bind("alpha", real, Bind("x", real, Bind("k", nat,
            Seq(Parenthesized(nonnegative), Sp, Rightarrow, Sp,
                Parenthesized(nowrap), Sp, Rightarrow, Sp, conclusion)))));
    }

    private static Formula Dotted(string owner, string name, Formula argument) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [argument]);

    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Q(string name) => Seq(Operatorname, Grp(Seq([.. name.Split('.').SelectMany((part, index) => index == 0 ? new Formula[] { F.Id(part) } : new Formula[] { Dot, part is "1" ? D(1) : F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
}
