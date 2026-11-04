using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalFiniteResolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFiniteResolution", H("Finite symbolic resolution of functional expressions"), Blocks(
            Describe.Lean(DescribeId.Create("finite-symbolic-resolution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution.original_finite_resolution"),
                H("Syntactic finite derivations and values forced in every solution"),
                ResolutionStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In the formula, Function(A,B) denotes functions from A to B, and isSome is the Boolean test for a defined optional result. This expression language has finite grounds, named finite or divergent parameter atoms, decorated state variables and ordered pairs. It has no independent literal Omega constructor. Undefined states may have arbitrary completed values. The compiler uses exactly as many rounds as there are original states; parameter atoms remain symbolic and are never expanded to a bounded family of values.")),
                    Paragraph(Text("Successful compilation is equivalent to a finite syntactic derivation from the defining expressions. A compiled finite expression evaluates to the same finite native tree in every solution at every parameter assignment. Repeated names, atomic coincidences, arbitrary powers and zero state or parameter counts are allowed. Stabilization follows because every nonstationary round adds a previously unresolved state.")),
                    Paragraph(Text("The conclusion does not construct a solution or identify semantic finiteness of a canonical solution. Literal Omega in the larger native source language is handled by a separate exact encoding with a fixed divergent internal slot, followed by decoding to the original finite parameter names. No external literature novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource ResolutionStatement()
    {
        var e = V("e");
        var f = V("f");
        var compile = FnCall("compile", V("E"), V("mode"), e);
        var complete = For(IffOf(EqOf(FnCall("isSome", compile), V("true")),
            FnCall("FiniteDerivation", V("E"), V("mode"), e)), ("e", Expressions));
        var value = EqOf(Value(V("v"), e), FnCall("embed", FnCall("finiteValue", V("p"), f)));
        var sound = For(Imp(EqOf(compile, FnCall("some", f)),
            For(Imp(Sol(V("E"), V("v")), value), ("p", Parameters), ("v", Vector))),
            ("e", Expressions), ("f", FiniteExpressions));
        return Statement(KM(For(And(complete, sound), ("E", Definitions), ("mode", Modes))));
    }

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat => V("Nat");
    private static Formula Fk => FnCall("Fin", V("k"));
    private static Formula Fm => FnCall("Fin", V("m"));
    private static Formula Expressions => FnCall("Expr", V("k"), V("m"));
    private static Formula Definitions => FnCall("Definitions", V("k"), V("m"));
    private static Formula Vector => FnCall("Function", Fm, V("CompletionTree"));
    private static Formula Modes => FnCall("Function", Fk, V("Bool"));
    private static Formula Parameters => FnCall("Function", Fk, Nat);
    private static Formula FiniteExpressions => FnCall("FiniteExpr", V("k"));
    private static Formula Par(Formula value) => StrataLint.Scribe.FormulaDsl.Seq(
        StrataLint.Scribe.FormulaDsl.Open, value, StrataLint.Scribe.FormulaDsl.Close);
    private static Formula FnCall(string name, params Formula[] arguments) =>
        new Formula.Apply(StrataLint.Scribe.FormulaDsl.Seq(
            StrataLint.Scribe.FormulaDsl.Operatorname,
            StrataLint.Scribe.FormulaDsl.Grp(V(name))), [.. arguments]);
    private static Formula EqOf(Formula left, Formula right) =>
        StrataLint.Scribe.FormulaDsl.Seq(left, StrataLint.Scribe.FormulaDsl.Sp,
            StrataLint.Scribe.FormulaDsl.Eq, StrataLint.Scribe.FormulaDsl.Sp, right);
    private static Formula Imp(Formula left, Formula right) =>
        StrataLint.Scribe.FormulaDsl.Seq(Par(left), StrataLint.Scribe.FormulaDsl.Sp,
            StrataLint.Scribe.FormulaDsl.Implies, StrataLint.Scribe.FormulaDsl.Sp, Par(right));
    private static Formula IffOf(Formula left, Formula right) =>
        StrataLint.Scribe.FormulaDsl.Seq(Par(left), StrataLint.Scribe.FormulaDsl.Sp,
            StrataLint.Scribe.FormulaDsl.Iff, StrataLint.Scribe.FormulaDsl.Sp, Par(right));
    private static Formula And(params Formula[] values) => StrataLint.Scribe.FormulaDsl.Seq(
        values.Select((value, index) => index == 0 ? Par(value) :
            StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Sp,
                StrataLint.Scribe.FormulaDsl.Land, StrataLint.Scribe.FormulaDsl.Sp, Par(value))).ToArray());
    private static Formula For(Formula body, params (string Name, Formula Type)[] binders)
    {
        foreach (var binder in binders.Reverse())
            body = StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Forall,
                StrataLint.Scribe.FormulaDsl.Sp, V(binder.Name), StrataLint.Scribe.FormulaDsl.Colon,
                StrataLint.Scribe.FormulaDsl.Sp, binder.Type, StrataLint.Scribe.FormulaDsl.Comma,
                StrataLint.Scribe.FormulaDsl.Sp, Par(body));
        return body;
    }
    private static Formula KM(Formula body) => For(body, ("k", Nat), ("m", Nat));
    private static Formula Value(Formula v, Formula e) => FnCall("value", V("mode"), V("p"), v, e);
    private static Formula Sol(Formula e, Formula v) => FnCall("Solution", e, V("mode"), V("p"), v);
    private static StatementSource Statement(Formula formula) => StatementSource.FromAuthor(
        StrataLint.Scribe.FormulaDsl.Disp(formula));

}
