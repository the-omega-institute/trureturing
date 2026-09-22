using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class TerminalPortFiveSplitCompatibilityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/wang2026port");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The terminal port (14,3,5) has nonzero local solutions at every prime but no "
            + "five-point of distinct primes above 5, refuting an abstracted joint "
            + "compatibility consequence of the cited five-splitting setup.",
        H("A Terminal-Port Five-Split Compatibility Counterexample"),
        Blocks(
            Paragraph(
                Text(
                    "The cited source separates a five-splitting prime-points hypothesis "
                        + "from its finite-local and positive-real-component inputs. The "
                        + "formal claim below existentially abstracts the real-side input as "
                        + "a predicate A and combines it with the local input. This is a "
                        + "repository-derived joint consequence, not a published statement "
                        + "quoted verbatim.")),
            Node(
                "terminal-port",
                "Terminal port",
                "Terminal",
                TerminalFormula(),
                "Terminal(R,c,p) requires positive natural R and c, a prime p, and "
                    + "c*p=R+1. The equality is the natural-number form of c*p-R=1; "
                    + "positivity prevents a truncated-subtraction reading from adding "
                    + "degenerate cases.",
                DescribeRole.Definition),
            Node(
                "five-split-form",
                "Five-split integer form",
                "form",
                FormFormula(),
                "The value of form(R,c,x) lies in Int. Every subtraction displayed here "
                    + "is integer subtraction: first R times the sum of the five complementary "
                    + "fourfold products is subtracted from c times the fivefold product, "
                    + "and then 1 is subtracted.",
                DescribeRole.Definition),
            Node(
                "local-unit-solubility",
                "Nonzero local solutions at every prime",
                "localUnits",
                LocalUnitsFormula(),
                "For each prime ell there is a five-tuple in ZMod(ell), every coordinate "
                    + "nonzero, satisfying the residue-field form equation. The subtraction "
                    + "in this formula is ZMod(ell) subtraction, not natural subtraction.",
                DescribeRole.Definition),
            Node(
                "five-prime-point",
                "Five distinct prime coordinates above the terminal prime",
                "primePoint",
                PrimePointFormula(),
                "A prime point is a natural five-tuple whose coordinates are prime, "
                    + "strictly greater than p, pairwise distinct, and annihilate the "
                    + "integer form.",
                DescribeRole.Definition),
            Node(
                "abstracted-joint-compatibility",
                "Abstracted joint compatibility claim",
                "claim",
                ClaimFormula(),
                "The quantified witness A has the full type Nat -> Nat -> Nat -> Prop. "
                    + "It must exist before the universal R,c,p quantifiers, must hold for "
                    + "every terminal port with R>4 and p>3, and together with local unit "
                    + "solubility must imply a five-prime point. No ambient-port premise is "
                    + "present in this formal claim.",
                DescribeRole.Definition),
            Node(
                "complementary-product-derivative",
                "Complementary-product list recurrence",
                "deriv",
                DerivFormula(),
                "The empty list has derivative 0. For q::xs, the recurrence adds the "
                    + "product of xs to q times the derivative of xs; for a five-entry "
                    + "list this is the sum of its five complementary fourfold products.",
                DescribeRole.Definition),
            Node(
                "natural-balance",
                "Natural balance equation",
                "Balance",
                BalanceFormula(),
                "Balance(R,C,xs) is the natural equality C*prod(xs)=R*deriv(xs)+1. "
                    + "It is the positive equality used to turn a zero of the integer form "
                    + "into the recursive search invariant.",
                DescribeRole.Definition),
            Node(
                "bounded-search-recurrence",
                "Bounded natural search",
                "search",
                SearchFormula(),
                "The recurrence uses NatDiv, NatMod, and NatSub throughout. NatSub(C*q,R) "
                    + "denotes the truncated natural subtraction in the definition; the proof "
                    + "establishes R<C*q before following every valid branch, so truncation "
                    + "does not alter a branch invariant. At a two-entry state the test n=0 "
                    + "makes the current primality check vacuous, and the one-entry case "
                    + "computes its final coordinate without a primality check. Thus the last "
                    + "two search levels deliberately relax primality, while search completeness "
                    + "still includes every actual sorted five-tuple of primes.",
                DescribeRole.Definition),
            Node(
                "joint-compatibility-refuted",
                "The abstracted joint compatibility claim is false",
                "result",
                ResultFormula(),
                "The witness (R,c,p)=(14,3,5) is terminal and satisfies R>4 and p>3. "
                    + "For every prime ell other than 5, the proof uses the nonzero residue "
                    + "tuple (5,1,-1,1,-1); at ell=5 it uses (1,1,-1,3,2). The completeness "
                    + "argument sorts any hypothetical five distinct prime coordinates above "
                    + "5 into the natural recurrence, while kernel evaluation gives "
                    + "search(5,14,3,5)=false. Hence no such prime tuple exists.",
                DescribeRole.Theorem,
                Paragraph(
                    Text(
                        "This terminal witness is nonambient in the cited source's sense. "
                            + "Evaluating squarefreeDeriv(14) from "),
                    Ref("D5/S3/PrimeForms/PrimaryPseudoperfectPorts"),
                    Text(
                        " gives 9, so 14-squarefreeDeriv(14)=5 rather than c=3. "
                            + "Accordingly, the theorem does not refute Hypothesis 19.2 "
                            + "for ambient terminal ports, does not refute an ambient-only "
                            + "method, and does not solve Erdos problem 313."))))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        DocumentBlock? additional = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source),
            additional is null
                ? Blocks(Paragraph(Text(prose)))
                : Blocks(Paragraph(Text(prose)), additional),
            role);

    private static Formula TerminalFormula()
    {
        var r = F.Id("R");
        var c = F.Id("c");
        var p = F.Id("p");
        return F.Disp(UniversalMany(
            [("R", Naturals()), ("c", Naturals()), ("p", Naturals())],
            Iff(
                Call("Terminal", r, c, p),
                And(
                    Less(F.D(0), r),
                    Less(F.D(0), c),
                    Call("Prime", p),
                    Equal(Multiply(c, p), Add(r, F.D(1)))))));
    }

    private static Formula FormFormula()
    {
        var r = F.Id("R");
        var c = F.Id("c");
        var x = F.Id("x");
        var value = Subtract(
            Subtract(
                Multiply(Call("IntCast", c), IndexedProduct(x, castToInt: true)),
                Multiply(Call("IntCast", r), ComplementarySum(x, castToInt: true))),
            F.D(1));
        return F.Disp(UniversalMany(
            [("R", Naturals()), ("c", Naturals()), ("x", FiveNaturals())],
            Equal(Call("form", r, c, x), value)));
    }

    private static Formula LocalUnitsFormula()
    {
        var r = F.Id("R");
        var c = F.Id("c");
        var ell = F.Id("ell");
        var x = F.Id("x");
        var i = F.Id("i");
        var equation = Equal(
            Subtract(
                Subtract(
                    Multiply(Call("ZModCast", c, ell), IndexedProduct(x, castToInt: false)),
                    Multiply(Call("ZModCast", r, ell), ComplementarySum(x, castToInt: false))),
                Call("ZModCast", F.D(1), ell)),
            Call("ZModCast", F.D(0), ell));
        var witness = Exists(
            "x",
            new Formula.TypeArrow(FinFive(), Call("ZMod", ell)),
            And(
                Universal("i", FinFive(), NotEqual(At(x, i), Call("ZModCast", F.D(0), ell))),
                equation));
        var body = Universal(
            "ell",
            Naturals(),
            Implies(Call("Prime", ell), witness));
        return F.Disp(UniversalMany(
            [("R", Naturals()), ("c", Naturals())],
            Iff(Call("localUnits", r, c), body)));
    }

    private static Formula PrimePointFormula()
    {
        var r = F.Id("R");
        var c = F.Id("c");
        var p = F.Id("p");
        var x = F.Id("x");
        var i = F.Id("i");
        var j = F.Id("j");
        var coordinates = Universal(
            "i",
            FinFive(),
            And(Call("Prime", At(x, i)), Less(p, At(x, i))));
        var distinct = UniversalMany(
            [("i", FinFive()), ("j", FinFive())],
            Implies(NotEqual(i, j), NotEqual(At(x, i), At(x, j))));
        var witness = Exists(
            "x",
            FiveNaturals(),
            And(coordinates, distinct, Equal(Call("form", r, c, x), F.D(0))));
        return F.Disp(UniversalMany(
            [("R", Naturals()), ("c", Naturals()), ("p", Naturals())],
            Iff(Call("primePoint", r, c, p), witness)));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("A");
        var r = F.Id("R");
        var c = F.Id("c");
        var p = F.Id("p");
        var applied = At(a, r, c, p);
        var consequence = Implies(
            applied,
            Call("localUnits", r, c),
            Call("primePoint", r, c, p));
        var body = UniversalMany(
            [("R", Naturals()), ("c", Naturals()), ("p", Naturals())],
            Implies(
                Call("Terminal", r, c, p),
                Less(F.D(4), r),
                Less(F.D(3), p),
                And(applied, consequence)));
        var predicateType = new Formula.TypeArrow(
            Naturals(),
            new Formula.TypeArrow(
                Naturals(),
                new Formula.TypeArrow(Naturals(), Propositions())));
        return F.Disp(Iff(F.Id("claim"), Exists("A", predicateType, body)));
    }

    private static Formula DerivFormula()
    {
        var q = F.Id("q");
        var xs = F.Id("xs");
        return F.Disp(new Formula.Aligned([
            Equal(Call("deriv", EmptyList()), F.D(0)),
            UniversalMany(
                [("q", Naturals()), ("xs", ListNaturals())],
                Equal(
                    Call("deriv", Cons(q, xs)),
                    Add(Call("prod", xs), Multiply(q, Call("deriv", xs))))),
        ]));
    }

    private static Formula BalanceFormula()
    {
        var r = F.Id("R");
        var c = F.Id("C");
        var xs = F.Id("xs");
        return F.Disp(UniversalMany(
            [("R", Naturals()), ("C", Naturals()), ("xs", ListNaturals())],
            Iff(
                Call("Balance", r, c, xs),
                Equal(
                    Multiply(c, Call("prod", xs)),
                    Add(Multiply(r, Call("deriv", xs)), F.D(1))))));
    }

    private static Formula SearchFormula()
    {
        var n = F.Id("n");
        var r = F.Id("R");
        var c = F.Id("C");
        var lo = F.Id("lo");
        var q = F.Id("q");
        var terminalQ = Call("NatDiv", Add(r, F.D(1)), c);
        var upper = Add(
            Call("NatDiv", Multiply(Add(n, F.D(2)), r), c),
            F.D(1));
        var recursiveBranch = Exists(
            "q",
            Naturals(),
            And(
                Less(q, upper),
                Less(lo, q),
                Or(Equal(n, F.D(0)), Call("Prime", q)),
                NotEqual(Call("NatMod", r, q), F.D(0)),
                Less(r, Multiply(c, q)),
                Equal(
                    Call(
                        "search",
                        Add(n, F.D(1)),
                        Multiply(r, q),
                        Call("NatSub", Multiply(c, q), r),
                        q),
                    True())));
        return F.Disp(new Formula.Aligned([
            UniversalMany(
                [("R", Naturals()), ("C", Naturals()), ("lo", Naturals())],
                Equal(Call("search", F.D(0), r, c, lo), False())),
            UniversalMany(
                [("R", Naturals()), ("C", Naturals()), ("lo", Naturals())],
                Iff(
                    Equal(Call("search", F.D(1), r, c, lo), True()),
                    And(
                        NotEqual(c, F.D(0)),
                        Less(lo, terminalQ),
                        Equal(Multiply(c, terminalQ), Add(r, F.D(1)))))),
            UniversalMany(
                [("n", Naturals()), ("R", Naturals()), ("C", Naturals()), ("lo", Naturals())],
                Iff(
                    Equal(Call("search", Add(n, F.D(2)), r, c, lo), True()),
                    And(NotEqual(c, F.D(0)), recursiveBranch))),
        ]));
    }

    private static Formula ResultFormula() =>
        F.Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula UniversalMany(
        (string Name, Formula Domain)[] variables,
        Formula body) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))],
            body);

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula IndexedProduct(Formula x, bool castToInt)
    {
        var i = F.Id("i");
        var value = At(x, i);
        if (castToInt)
        {
            value = Call("IntCast", value);
        }
        return F.Seq(
            F.Prod,
            F.Underscore,
            F.Grp(i, F.Sp, F.InMacro, F.Sp, FinFive()),
            F.Sp,
            value);
    }

    private static Formula ComplementarySum(Formula x, bool castToInt)
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var value = At(x, j);
        if (castToInt)
        {
            value = Call("IntCast", value);
        }
        var product = F.Seq(
            F.Prod,
            F.Underscore,
            F.Grp(
                j,
                F.Sp,
                F.InMacro,
                F.Sp,
                FinFive(),
                F.Comma,
                F.Sp,
                j,
                F.Sp,
                F.Neq,
                F.Sp,
                i),
            F.Sp,
            value);
        return F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(i, F.Sp, F.InMacro, F.Sp, FinFive()),
            F.Sp,
            product);
    }

    private static Formula And(params Formula[] clauses) =>
        FoldLogic(FormulaLogicOperator.And, clauses);

    private static Formula Or(params Formula[] clauses) =>
        FoldLogic(FormulaLogicOperator.Or, clauses);

    private static Formula Implies(params Formula[] clauses) =>
        FoldLogic(FormulaLogicOperator.Implies, clauses);

    private static Formula FoldLogic(FormulaLogicOperator operation, Formula[] clauses)
    {
        if (clauses.Length < 2)
        {
            throw new ArgumentException("At least two clauses are required.", nameof(clauses));
        }
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]),
                operation,
                result);
        }
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) =>
        F.Seq(F.Open, value, F.Close);

    private static Formula EmptyList() => F.Seq(F.OpenBracket, F.CloseBracket);

    private static Formula Cons(Formula head, Formula tail) =>
        F.Seq(head, F.Sp, F.Colon, F.Colon, F.Sp, tail);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Propositions() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Prop"));

    private static Formula ListNaturals() => Call("List", Naturals());

    private static Formula FinFive() => Call("Fin", F.D(5));

    private static Formula FiveNaturals() =>
        new Formula.TypeArrow(FinFive(), Naturals());

    private static Formula True() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("true"));

    private static Formula False() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("false"));
}
