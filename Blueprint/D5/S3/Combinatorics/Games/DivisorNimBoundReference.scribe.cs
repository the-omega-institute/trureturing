using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundReferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundReference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A distinguished heap bounds removal amounts and divisor counts. Separating "
            + "moves that preserve this heap from moves that replace it gives a uniform "
            + "recurrence for the Sprague–Grundy value.",
        H("Bounds from a Distinguished Heap"),
        Blocks(
            Node("removal-ceiling", "The reference heap bounds every removal", "removal_le_reference",
                "A removal from the reference heap is at most its size. A removal "
                    + "elsewhere divides that positive size and is therefore no larger."),
            Node("reference-survives", "An unchanged reference heap survives", "reference_survives",
                "Changing a different heap retains the reference occurrence."),
            Node("reference-changes", "A positive remainder is retained", "changed_reference",
                "A removal smaller than the changed heap leaves its positive remainder in the board."),
            Node("lower-reference", "Lower removals retain a reference ceiling", "lower_reference",
                "A lower-depth removal cannot empty the changed heap. Either the original "
                    + "reference survives or its positive remainder is no larger."),
            Node("dyadic-step", "Counting high-depth removals", "dyadic_step",
                "For a nonzero parent, a nonzero high-depth follower changes its unique "
                    + "minimum-depth heap. A finite set of eligible removal amounts bounds "
                    + "the number of exceptional followers."),
            Node("coarse-zero", "The coarse ceiling at depth zero", "coarseBound_zero",
                "The depth-zero ceiling is H plus one."),
            Node("coarse-successor", "Successive coarse ceilings", "coarseBound_succ",
                "The next ceiling adds the number of positive multiples of the next "
                    + "depth power that fit below H, followed by one mex increment."),
            Node("coarse-monotone", "The coarse ceiling increases with depth", "coarseBound_mono",
                "Every increment is nonnegative."),
            Node("coarse-balance", "The divisible geometric sum", "coarseBound_balance",
                "When the depth power divides H, the geometric sum and its last quotient "
                    + "add to twice H, with the depth-dependent mex increments."),
            Node("coarse-reference", "Large odd factors suffice", "coarseBound_le_reference",
                "If the odd factor is at least v plus one, the terminal quotient absorbs "
                    + "all depth-dependent increments and the ceiling is at most twice the heap."),
            Node("changed-coarse", "The ceiling after changing the reference", "changed_coarseBound",
                "Subtracting the smallest amount of valuation j from the reference gives "
                    + "the explicit changed-reference ceiling."),
            Node("coarse-bound", "A uniform coarse Grundy bound", "coarse_bound",
                "Induction on depth bounds lower-depth followers. Higher-depth nonzero "
                    + "followers can arise only on a unique minimum heap, and their removal "
                    + "amounts are multiples of the depth power bounded by H."),
            Node("high-divisors", "Divisors above a dyadic threshold", "highDivisors",
                "Keep divisors of m that are multiples of the depth power.", DescribeRole.Definition),
            Node("quotient-divisors", "Division injects eligible removals into quotient divisors",
                "highDivisors_card_le_quotient",
                "Dividing an eligible removal by the depth power gives a divisor of the "
                    + "reference quotient. Multiplication by that power recovers the removal."),
            Node("divisor-product", "A divisor-count product bound", "divisor_card_le",
                "Every divisor of a product is a product of divisors. The power of two "
                    + "has w plus one divisors, which bounds the cardinality by the product."),
            Node("high-divisor-count", "The high-removal divisor ceiling", "highDivisors_card_le",
                "The quotient has the remaining power of two and the original odd factor, "
                    + "giving at most v minus k plus one times the odd-factor divisor count."),
            Node("reference-valuation", "The depth of the distinguished heap", "reference_valuation",
                "Multiplication by a positive odd factor leaves the valuation of the power of two unchanged."),
            Node("reference-lower", "Lower-depth followers preserve or change the reference",
                "reference_lower",
                "An unchanged reference invokes the earlier distinguished-heap bound. "
                    + "A changed reference invokes the coarse ceiling for its smaller remainder."),
            Node("reference-step", "The distinguished-heap recurrence step", "reference_step",
                "Below the reference valuation, high removals divide the unchanged reference. "
                    + "At its valuation, high removals on the unique minimum are multiples "
                    + "of its depth power fitting within its size."),
            Node("reference-bound", "The recurrence bounds every containing board", "reference_bound",
                "Strong induction on depth combines all earlier containing-board bounds "
                    + "with the changed-reference ceilings. The number of other heaps is unrestricted.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(FormulaFor(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Position() => Call("Multiset", Nat());
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] items)
    {
        var result = items[^1];
        for (var i = items.Length - 2; i >= 0; --i)
            result = new Formula.Logic(items[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) =>
        Call("div", a, b);
    private static Formula Mem(Formula a, Formula b) => Call("mem", a, b);
    private static Formula Power(Formula k) => Seq(D(2), Caret, Grp(k));
    private static Formula Val(Formula h) => Call("valuation", h);
    private static Formula Depth(Formula p, Formula k) => Call("HasDepth", p, k);
    private static Formula Grundy(Formula p) => Call("grundy", p);
    private static Formula Next(Formula p, Formula h, Formula d) => Call("successor", p, h, d);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Coarse(Formula k, Formula h) => Call("coarseBound", k, h);
    private static Formula Nats(Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; --i) body = All(names[i], Nat(), body);
        return body;
    }

    private static Formula FormulaFor(string declaration)
    {
        var p = F.Id("P"); var q = F.Id("Q"); var h = F.Id("h"); var d = F.Id("d");
        var m = F.Id("m"); var ceiling = F.Id("H"); var k = F.Id("k"); var j = F.Id("j");
        var v = F.Id("v"); var u = F.Id("u"); var b = F.Id("B"); var e = F.Id("e");
        var a = F.Id("A"); var w = F.Id("w"); var n = F.Id("n");
        var reference = Mul(Power(v), u);
        var positive = Call("Positive", p);
        var legal = Call("legal", p, h, d);
        var changed = Call("changedBound", v, u, j);
        var odd = Eq(Call("mod", u, D(2)), D(1));
        var referencePremise = And(positive, Depth(p, k), Mem(reference, p),
            Lt(D(0), u), odd, Le(k, v));
        var earlier = All("Q", Position(), All("j", Nat(),
            Imp(And(Call("Positive", q), Lt(j, k), Depth(q, j), Mem(reference, q)),
                Le(Grundy(q), b))));
        var changedCeilings = All("j", Nat(), Imp(Lt(j, k), Le(changed, b)));
        var lowFollowers = All("h", Nat(), All("d", Nat(),
            Imp(And(Mem(h, p), legal, Lt(Val(d), k)), Le(Grundy(Next(p, h, d)), b))));
        Formula body;
        if (declaration == "removal_le_reference")
        {
                body = All("P", Position(), Nats(Imp(And(positive, Mem(m, p),
                    Le(m, ceiling), legal), Le(d, ceiling)), "h", "d", "m", "H"));
        }
        else if (declaration == "reference_survives")
        {
                body = All("P", Position(), Nats(Imp(And(Mem(m, p), Ne(m, h)),
                    Mem(m, Next(p, h, d))), "h", "d", "m"));
        }
        else if (declaration == "changed_reference")
        {
                body = All("P", Position(), Nats(Imp(Lt(d, h),
                    Mem(Sub(h, d), Next(p, h, d))), "h", "d"));
        }
        else if (declaration == "lower_reference")
        {
                body = All("P", Position(), Nats(Imp(And(positive, Depth(p, k),
                    Mem(h, p), Mem(m, p), Le(m, ceiling), legal, Lt(Val(d), k)),
                    Exists("n", Nat(), And(Mem(n, Next(p, h, d)), Le(n, ceiling)))),
                    "h", "d", "m", "H", "k"));
        }
        else if (declaration == "dyadic_step")
        {
                var high = All("d", Nat(), Imp(And(Call("legal", p, e, d), Le(k, Val(d))), Mem(d, a)));
                body = All("P", Position(), Nats(All("A", Call("Finset", Nat()),
                    Imp(And(positive, Depth(p, k), Mem(e, p), Eq(Val(e), k), lowFollowers, high),
                        Le(Grundy(p), Add(Add(b, Card(a)), D(1))))), "k", "e", "B"));
        }
        else if (declaration == "coarseBound_zero")
        {
                body = All("H", Nat(), Eq(Coarse(D(0), ceiling), Add(ceiling, D(1))));
        }
        else if (declaration == "coarseBound_succ")
        {
                body = Nats(Eq(Coarse(Add(k, D(1)), ceiling),
                    Add(Add(Coarse(k, ceiling), Div(ceiling, Power(Add(k, D(1))))), D(1))), "k", "H");
        }
        else if (declaration == "coarseBound_mono")
        {
                body = Nats(Imp(Le(j, k), Le(Coarse(j, ceiling), Coarse(k, ceiling))), "H", "j", "k");
        }
        else if (declaration == "coarseBound_balance")
        {
                body = Nats(Imp(Call("dvd", Power(k), ceiling),
                    Eq(Add(Coarse(k, ceiling), Div(ceiling, Power(k))),
                        Add(Add(Mul(D(2), ceiling), k), D(1)))), "k", "H");
        }
        else if (declaration == "coarseBound_le_reference")
        {
                body = Nats(Imp(And(Lt(D(0), u), Le(k, v), Le(Add(v, D(1)), u)),
                    Le(Coarse(k, reference), Mul(D(2), reference))), "v", "u", "k");
        }
        else if (declaration == "changed_coarseBound")
        {
                body = Nats(Imp(And(Lt(D(0), u), Lt(j, v)),
                    Eq(Coarse(j, Sub(reference, Power(j))), changed)), "v", "u", "j");
        }
        else if (declaration == "coarse_bound")
        {
                body = All("P", Position(), Nats(Imp(And(positive, Depth(p, k),
                    Mem(m, p), Le(m, ceiling)), Le(Grundy(p), Coarse(k, ceiling))), "k", "m", "H"));
        }
        else if (declaration == "highDivisors")
        {
                var set = Seq(OpenBrace, d, Sp, InMacro, Sp, Call("divisors", m), Sp, Bar, Sp,
                    Call("dvd", Power(k), d), CloseBrace);
                body = Nats(Eq(Call("highDivisors", m, k), set), "m", "k");
        }
        else if (declaration == "highDivisors_card_le_quotient")
        {
                body = Nats(Imp(And(Lt(D(0), m), Call("dvd", Power(k), m)),
                    Le(Card(Call("highDivisors", m, k)), Card(Call("divisors", Div(m, Power(k)))))), "m", "k");
        }
        else if (declaration == "divisor_card_le")
        {
                body = Nats(Le(Card(Call("divisors", Mul(Power(w), u))),
                    Mul(Add(w, D(1)), Call("oddDivisorCount", u))), "w", "u");
        }
        else if (declaration == "highDivisors_card_le")
        {
                body = Nats(Imp(And(Lt(D(0), u), Le(k, v)),
                    Le(Card(Call("highDivisors", reference, k)),
                        Mul(Add(Sub(v, k), D(1)), Call("oddDivisorCount", u)))), "v", "u", "k");
        }
        else if (declaration == "reference_valuation")
        {
                body = Nats(Imp(And(Lt(D(0), u), odd), Eq(Val(reference), v)), "v", "u");
        }
        else if (declaration == "reference_lower")
        {
                body = All("P", Position(), Nats(Imp(And(referencePremise, earlier, changedCeilings),
                    lowFollowers), "v", "u", "k", "B"));
        }
        else if (declaration == "reference_step")
        {
                body = All("P", Position(), Nats(Imp(And(referencePremise, earlier, changedCeilings),
                    Le(Grundy(p), Add(Add(b, Call("exceptionalCount", v, u, k)), D(1)))),
                    "v", "u", "k", "B"));
        }
        else
        {
                body = All("P", Position(), Nats(Imp(And(referencePremise, Lt(D(0), v)),
                    Le(Grundy(p), Call("recurrenceBound", v, u, k))), "v", "u", "k"));
        }
        return Disp(body);
    }
}
