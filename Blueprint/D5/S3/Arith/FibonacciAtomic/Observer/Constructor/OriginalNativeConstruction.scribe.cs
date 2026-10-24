using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalNativeConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalNativeConstruction", H("Native completed solutions of functional cases"), Blocks(
            Describe.Lean(DescribeId.Create("native-simultaneous-equations"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_solution"),
                H("The native corecursor satisfies every simultaneous equation"),
                SolutionStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In the formulas, Function(A,B) denotes functions from A to B. For a system with no variable at a defining root, the constructed native vector satisfies every definition and agrees exactly with the supplied completed assignment at every undefined state. Constants and literal Omega are permitted defining roots; recursive state occurrences are below pairs. The root-link normalization theorem derives this shape from the original functional system."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-conditional-uniqueness"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_unique"),
                H("Uniqueness conditional on all free values"),
                UniquenessStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every native solution with the given free assignment equals the constructed vector. Expression evaluation is a coalgebra morphism: the source equations justify each defined root, the free assignment justifies every undefined root, and ordered-pair children retain the same expression valuation. Final-coalgebra uniqueness then applies to this concrete native morphism."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-native-construction"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.original_native_construction"),
                H("Simultaneous construction, conditional uniqueness and exact reconstruction"),
                ConstructionStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input is any finite functional system in the literal-Omega source syntax. Normalization and its reconstruction are obtained from that system and do not depend on parameters. There is no assumed normalized presentation or supplied solution. The conclusions hold for all natural parameter values and therefore for every value satisfying the retained arithmetic guard.")),
                    Paragraph(Text("The function native is an actual corecursor into the existing unrestricted CompletionTree. Its states are displayed expressions or native trees being copied. A defined pair emits an ordered native branch immediately. Fixed powers distribute over that branch using the actual substitution rho. Finite grounds, parameter atoms, literal Omega and arbitrary completed free assignments use their actual native values. The proof establishes composition with fixed powers and expression evaluation before deriving the simultaneous equations.")),
                    Paragraph(Text("For each assignment to undefined normalized states, native satisfies the normalized equations and has exactly those free values. It is the unique normalized solution with that assignment, by the instantiated final-coalgebra morphism law. Reconstructing it gives an original solution. Every original solution restricts to a normalized solution and is recovered by the same construction with its own free values. Erased state names may remain as unused normalized coordinates; their supplied values do not create additional original choices.")),
                    Paragraph(Text("Assigning the actual Omega to every normalized free coordinate selects a canonical original solution. Applying the retained reconstruction to each original residual preserves its full native value. All state and parameter counts, bare links, zero alias cycles and positive root cycles remain in scope. This canonical selection is a semantic construction; effective prefix computation and a complete semantic finiteness classifier require additional conclusions.")),
                    Paragraph(Text("The finite compiler is reused through a total internal encoding. Original parameter indices are shifted injectively, while one fixed divergent slot represents literal Omega, including at zero original parameters. This slot is representation data and is always interpreted divergently; its natural placeholder is fixed to zero. Decoding finite outputs removes it and returns expressions using only original grounds, parameters, powers and pairs. Every successful compilation is forced in every original solution, including the constructed one. Failure of this finite test is not asserted to imply canonical infinity.")),
                    Paragraph(Text("The mathematical inputs are native root-link normalization, the existing finite-resolution theorem, the native substitution identities and the pinned polynomial-functor final coalgebra. No free unary substitution, bare-drift contraction, bounded rank, satisfiability assumption or supplied fixed point is used. No external novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource SolutionStatement()
    {
        var n = Native(V("E"), V("g"));
        var body = For(And(Sol(V("E"), n), Free(V("E"), n, V("g"))),
            ("mode", Modes), ("p", Parameters), ("g", Vector));
        return Statement(KM(For(Imp(FnCall("PairGuarded", V("E")), body), ("E", Definitions))));
    }

    private static StatementSource UniquenessStatement()
    {
        var body = For(Imp(And(Sol(V("E"), V("v")), Free(V("E"), V("v"), V("g"))),
            EqOf(V("v"), Native(V("E"), V("g")))),
            ("mode", Modes), ("p", Parameters), ("g", Vector), ("v", Vector));
        return Statement(KM(For(Imp(FnCall("PairGuarded", V("E")), body), ("E", Definitions))));
    }

    private static StatementSource ConstructionStatement()
    {
        var n = V("N");
        var r = V("R");
        var g = V("g");
        var v = V("v");
        var u = V("u");
        var forward = For(Sol(V("E"), Rec(r, Native(n, g))), ("g", Vector));
        var backward = For(Imp(Sol(V("E"), v), And(Sol(n, v),
            EqOf(Rec(r, v), v), EqOf(Rec(r, Native(n, v)), v))), ("v", Vector));
        var unique = For(Imp(Sol(n, u), Imp(Free(n, u, g), EqOf(u, Native(n, g)))),
            ("g", Vector), ("u", Vector));
        var equations = For(And(Sol(n, Native(n, g)), Free(n, Native(n, g), g)), ("g", Vector));
        var finite = For(Imp(EqOf(FnCall("finiteCompile", V("E"), V("mode"), V("e")),
            FnCall("some", V("f"))), For(Imp(Sol(V("E"), v),
                EqOf(Value(v, V("e")), FnCall("embed", FnCall("finiteValue", V("p"), V("f"))))),
                ("v", Vector))), ("e", Expressions), ("f", FiniteExpressions));
        var body = Some("N", Definitions, Some("R", Reconstructions, And(FnCall("PairGuarded", n),
            For(And(forward, backward, unique, equations, finite), ("mode", Modes), ("p", Parameters)))));
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
    private static Formula FiniteExpressions => FnCall("FiniteExpr", V("k"));
    private static Formula Par(Formula value) => StrataLint.Scribe.FormulaDsl.Seq(
        StrataLint.Scribe.FormulaDsl.Open, value, StrataLint.Scribe.FormulaDsl.Close);
    private static Formula FnCall(string name, params Formula[] arguments) =>
        new Formula.Apply(StrataLint.Scribe.FormulaDsl.Seq(
            StrataLint.Scribe.FormulaDsl.Operatorname,
            StrataLint.Scribe.FormulaDsl.Grp(V(name))), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
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
    private static Formula Native(Formula e, Formula g) => FnCall("native", e, V("mode"), V("p"), g);
    private static Formula Free(Formula e, Formula u, Formula g) => For(
        Imp(EqOf(App(e, V("i")), V("none")), EqOf(App(u, V("i")), App(g, V("i")))), ("i", Fm));
    private static StatementSource Statement(Formula formula) => StatementSource.FromAuthor(
        StrataLint.Scribe.FormulaDsl.Disp(formula));

}
