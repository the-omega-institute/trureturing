using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalFunctionalNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFunctionalNormalization", H("Functional native expressions and root links"), Blocks(
            Describe.Lean(DescribeId.Create("native-fixed-powers"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_power"),
                H("Distribution of every fixed native power"), PowerStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In the formulas, Function(A,B) is the type of functions from A to B, and rhoIterate(a,X) is the a-fold native substitution of X. Expressions retain finite grounds, named parameter atoms, a literal Omega, decorated state variables and ordered pairs. A parameter name has its fixed finite or divergent mode. Literal Omega is available even when there are no parameters. The power operation distributes the actual native substitution over pairs, composes variable decorations, shifts finite atoms and evaluates finite grounds. It introduces no independent unary tree constructor."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-substitution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_subst"),
                H("Simultaneous substitution preserves evaluation"), SubstitutionStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A reconstruction is one expression for each original state name. Simultaneous substitution evaluates that expression with the same valuation at every occurrence. Parameter names and their coincidences are retained; ordered pairs may evaluate to atomic values. FunctionalCase also retains the arithmetic guard and a finite family of expressions for every designated original residual."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-link-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.root_link_normalization"),
                H("Exact elimination of all defining root links"), NormalizationStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A functional system has at most one defining expression for each state; undefined states remain unrestricted. The normalized system has no decorated variable as a defining root. Its remaining state occurrences are strictly below a pair. Every normalized solution reconstructs an original solution. Conversely, an original solution satisfies the normalized equations and is fixed by reconstruction. Substituting the same reconstruction into every designated residual preserves all original coordinates.")),
                    Paragraph(Text("Eliminating a nonself link substitutes its decorated target everywhere and retains its reconstruction. A zero self-link imposes no condition and becomes free. A positive self-link forces the actual leafless Omega: iteration of its positive period and native eventual full prefixes exclude every leaf. Each elimination strictly decreases the finite set of root-link definitions. The function normalize computes the least remaining root link and its explicit substitution at each step. Thus normalization needs no supplied graph rank, finite expansion bound, solvability premise or fixed point.")),
                    Paragraph(Text("The system and reconstruction depend on syntax alone, independently of natural parameter values. Both semantic directions hold for all finite state and parameter counts, including zero, with unrestricted completed free values. The arithmetic guard is retained as a condition on the original parameter tuple; it is never replaced by existence of a solution. This is a native semantic normalization result, with no external novelty claim."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource PowerStatement()
    {
        var e = V("e");
        var body = EqOf(Value(V("v"), FnCall("power", V("a"), e)),
            FnCall("rhoIterate", V("a"), Value(V("v"), e)));
        return Statement(KM(For(body, ("mode", Modes), ("p", Parameters),
            ("v", Vector), ("a", Nat), ("e", Expressions))));
    }

    private static StatementSource SubstitutionStatement()
    {
        var body = EqOf(Value(V("v"), FnCall("subst", V("s"), V("e"))),
            Value(Rec(V("s"), V("v")), V("e")));
        return Statement(KM(For(body, ("mode", Modes), ("p", Parameters),
            ("v", Vector), ("s", Reconstructions), ("e", Expressions))));
    }

    private static StatementSource NormalizationStatement()
    {
        var n = V("N");
        var r = V("R");
        var forward = For(Imp(Sol(n, V("u")), Sol(V("E"), Rec(r, V("u")))),
            ("mode", Modes), ("p", Parameters), ("u", Vector));
        var backward = For(Imp(Sol(V("E"), V("v")),
            And(Sol(n, V("v")), EqOf(Rec(r, V("v")), V("v")))),
            ("mode", Modes), ("p", Parameters), ("v", Vector));
        var body = Some("N", Definitions, Some("R", Reconstructions,
            And(FnCall("PairGuarded", n), forward, backward)));
        return Statement(KM(For(body, ("E", Definitions))));
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
    private static Formula Reconstructions => FnCall("Function", Fm, Expressions);
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
    private static Formula Some(string name, Formula type, Formula body) =>
        StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Exists,
            StrataLint.Scribe.FormulaDsl.Sp, V(name), StrataLint.Scribe.FormulaDsl.Colon,
            StrataLint.Scribe.FormulaDsl.Sp, type, StrataLint.Scribe.FormulaDsl.Comma,
            StrataLint.Scribe.FormulaDsl.Sp, Par(body));
    private static Formula KM(Formula body) => For(body, ("k", Nat), ("m", Nat));
    private static Formula Value(Formula v, Formula e) => FnCall("value", V("mode"), V("p"), v, e);
    private static Formula Sol(Formula e, Formula v) => FnCall("Solution", e, V("mode"), V("p"), v);
    private static Formula Rec(Formula r, Formula v) => FnCall("reconstruct", V("mode"), V("p"), r, v);
    private static StatementSource Statement(Formula formula) => StatementSource.FromAuthor(
        StrataLint.Scribe.FormulaDsl.Disp(formula));

}
