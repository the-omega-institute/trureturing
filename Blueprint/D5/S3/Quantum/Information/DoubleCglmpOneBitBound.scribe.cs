using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class DoubleCglmpOneBitBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DoubleCglmpOneBitBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/marton2023onebit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every d >= 2, two parallel copies of the CGLMP_d game have one-bit classical bound 12 when one bit is sent from Alice to Bob, and also when it is sent from Bob to Alice; the truncations to the inputs {00, 01, 11} x {00, 01, 11} and {00, 01, 11} x {00, 11} have local bounds 7 and 4. These are the conjecture and the two conjectured local bounds of I. Márton, E. Bene, P. Diviánszky and T. Vértesi (arXiv:2308.10771), who verified them up to d = 10 and d = 20.",
        H("The one-bit bound of the double CGLMP game"),
        Blocks(
            Node("inputs", "Inputs of the double game", Disp(Equal(F.Id("Inp"),
                    Seq(FinOf(2), Sp, Times, Sp, FinOf(2)))),
                "An input of the double game is the pair of input bits (x, x') of the two copies; outputs are pairs in Fin d x Fin d.",
                "Inp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("copy", "Winning one copy", CopyFormula(),
                "Eq. (cglmpineq) of the paper: CGLMP_d = P(A_0 >= B_0) + P(A_0 <= B_1) + P(A_1 < B_0) + P(A_1 >= B_1), read as a game won on inputs (x, y) and outputs (a, b) in the four listed cases.",
                "copyWins", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("wins", "Winning the double game", WinsFormula(),
                "Two copies are played in parallel; the double game is won when both copies are won.",
                "wins", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bell", "The Bell expression", BellFormula(),
                "The Bell expression CGLMP_d tensor CGLMP_d restricted to the inputs XS x YS: the total probability of winning, where [wins] is 1 when the double game is won and 0 otherwise.",
                "bell", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("response", "Response distributions", ResponseFormula(),
                "A conditional distribution of an output given the hidden value t: measurable in t, nonnegative and normalised.",
                "IsResponse", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("local", "Local behaviours", LocalFormula(),
                "Eq. (P_LHV): the hidden variable has an arbitrary probability distribution mu on the real line, and each party answers with a response distribution depending on its own input and t.",
                "IsLocal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onebit-ab", "One bit from Alice to Bob", OneBitAbFormula(),
                "Eq. (P_LHV1bit): in addition Alice sends a bit l(X, t), measurable in t, and Bob's response depends on it.",
                "IsOneBitAB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onebit-ba", "One bit from Bob to Alice", OneBitBaFormula(),
                "The same with the bit l(Y, t) sent from Bob to Alice; the paper lists this game as bidirectional.",
                "IsOneBitBA", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sym", "The inputs of the truncations", InputSetFormula("symInputs", [(0, 0), (0, 1), (1, 1)]),
                "The inputs {00, 01, 11} kept by both truncations.",
                "symInputs", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("asym", "Bob's inputs of the asymmetric truncation", InputSetFormula("asymInputs", [(0, 0), (1, 1)]),
                "Bob's inputs {00, 11} of the asymmetric truncation.",
                "asymInputs", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture and the two conjectured local bounds", ClaimFormula(),
                "For every d >= 2: the one-bit bound of the double game is 12 in both directions, the local bound of the truncation to {00, 01, 11} x {00, 01, 11} is 7, and that of the truncation to {00, 01, 11} x {00, 11} is 4. Each bound is the greatest value of the Bell expression over the class.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the three bounds", Disp(F.Id("claim")),
                "Take inputs U, V of Alice whose bits in one copy are 0 and 1, and inputs W, Z of Bob whose bits in that copy are 0 and 1. The four winning conditions of that copy would give a_U <= b_Z <= a_V < b_W <= a_U, so they cannot all hold: in every such rectangle {U, V} x {W, Z} on which Bob answers alike, some cell is lost. A kernel-checked count over the Boolean patterns of won cells shows that three inputs of one party that send the same message lose at least four of their twelve cells, and two such inputs lose at least two of their eight; splitting Alice's (or Bob's) inputs by the message they send, at most 12 of the 16 cells are won, and at most 7 and 4 in the truncations. For a fixed hidden value the Bell expression is linear in each response distribution, so replacing each by a best output does not decrease it; the value at each t is therefore at most the deterministic bound, and integrating over mu gives the bound for the class. Deterministic strategies with outputs 0 and 1 and a point mass attain 12, 12, 7 and 4, for every d >= 2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("marton-2023-double-cglmp-one-bit-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cglmp-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(F.Id(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula AndAll(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula OrAll(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.Or, result);
        return result;
    }
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula SomeOver(Formula variables, Formula domain, Formula body) =>
        Seq(Exists, Sp, variables, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Times2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Bools() => F.Id("Bool");
    private static Formula FinOf(byte n) => Call("Fin", D(n));
    private static Formula Out() => Seq(Call("Fin", F.Id("d")), Sp, Times, Sp, Call("Fin", F.Id("d")));
    private static Formula Arrow(params Formula[] parts)
    {
        var items = new List<Formula> { parts[0] };
        foreach (var part in parts[1..])
            items.AddRange([Sp, To, Sp, part]);
        return Seq([.. items]);
    }
    private static Formula Sub(string name, string index) => new Formula.Subscript(F.Id(name), F.Id(index));
    private static Formula SubD(Formula baseName, byte index) => new Formula.Subscript(baseName, D(index));
    private static Formula Resp(string party, params Formula[] arguments) =>
        new Formula.Apply(Sub("p", party), [.. arguments]);
    private static Formula Integral(Formula integrand) =>
        Seq(Int, Sp, integrand, Sp, F.Id("d"), Mu, Parenthesized(F.Id("t")));
    private static Formula Pair(byte x, byte y) => Seq(Open, D(x), Comma, Sp, D(y), Close);

    private static Formula CopyFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula le(Formula l, Formula r) => Rel(l, FormulaRelationOperator.LessThanOrEqual, r);
        Formula lt(Formula l, Formula r) => Rel(l, FormulaRelationOperator.LessThan, r);
        Formula body = OrAll(
            AndAll(Equal(x, D(0)), Equal(y, D(0)), le(b, a)),
            AndAll(Equal(x, D(0)), Equal(y, D(1)), le(a, b)),
            AndAll(Equal(x, D(1)), Equal(y, D(0)), lt(a, b)),
            AndAll(Equal(x, D(1)), Equal(y, D(1)), le(b, a)));
        return Disp(Iff(Call("copyWins", x, y, a, b), body));
    }

    private static Formula WinsFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), A = F.Id("A"), B = F.Id("B");
        Formula copy(byte i) => Call("copyWins", SubD(X, i), SubD(Y, i), SubD(A, i), SubD(B, i));
        return Disp(Iff(Call("wins", X, Y, A, B), AndAll(copy(1), copy(2))));
    }

    private static Formula BellFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), A = F.Id("A"), B = F.Id("B"), P = F.Id("P");
        Formula indicator = Seq(OpenBracket, Call("wins", X, Y, A, B), CloseBracket);
        Formula term = Times2(indicator, new Formula.Apply(P, [X, Y, A, B]));
        Formula body = SumOver(Member(X, F.Id("XS")), SumOver(Member(Y, F.Id("YS")),
            SumOver(A, SumOver(B, term))));
        return Disp(Equal(Call("bell", F.Id("XS"), F.Id("YS"), P), body));
    }

    private static Formula ResponseFormula()
    {
        Formula r = F.Id("r"), t = F.Id("t"), A = F.Id("A");
        Formula rt = new Formula.Apply(r, [t, A]);
        Formula measurable = All("A", Out(), Call("Measurable",
            Parenthesized(Seq(t, Sp, Mapsto, Sp, rt))));
        Formula nonnegative = All("t", Reals(), All("A", Out(),
            Rel(D(0), FormulaRelationOperator.LessThanOrEqual, rt)));
        Formula normalised = All("t", Reals(), Equal(SumOver(A, rt), D(1)));
        return Disp(Iff(Call("IsResponse", r), AndAll(measurable, nonnegative, normalised)));
    }

    private static Formula ProbabilityPrefix(Formula body)
    {
        Formula mu = Mu;
        return SomeOver(mu, Call("Measure", Reals()), AndAll(Call("IsProbabilityMeasure", mu), body));
    }

    private static Formula LocalFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), A = F.Id("A"), B = F.Id("B"), t = F.Id("t");
        Formula responses = Seq(Sub("p", "A"), Comma, Sp, Sub("p", "B"));
        Formula type = Arrow(F.Id("Inp"), Reals(), Out(), Reals());
        Formula integral = Integral(Times2(Resp("A", X, t, A), Resp("B", Y, t, B)));
        Formula behaviour = All("X", F.Id("Inp"), All("Y", F.Id("Inp"), All("A", Out(), All("B", Out(),
            Equal(new Formula.Apply(F.Id("P"), [X, Y, A, B]), integral)))));
        Formula body = SomeOver(responses, type, AndAll(
            All("X", F.Id("Inp"), Call("IsResponse", new Formula.Apply(Sub("p", "A"), [X]))),
            All("Y", F.Id("Inp"), Call("IsResponse", new Formula.Apply(Sub("p", "B"), [Y]))),
            behaviour));
        return Disp(Iff(Call("IsLocal", F.Id("d"), F.Id("P")), ProbabilityPrefix(body)));
    }

    private static Formula OneBitAbFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), A = F.Id("A"), B = F.Id("B"), t = F.Id("t"), m = F.Id("m");
        Formula lXt = new Formula.Apply(F.Id("l"), [X, t]);
        Formula integral = Integral(Times2(Resp("A", X, t, A), Resp("B", Y, lXt, t, B)));
        Formula behaviour = All("X", F.Id("Inp"), All("Y", F.Id("Inp"), All("A", Out(), All("B", Out(),
            Equal(new Formula.Apply(F.Id("P"), [X, Y, A, B]), integral)))));
        Formula body = SomeOver(Sub("p", "A"), Arrow(F.Id("Inp"), Reals(), Out(), Reals()),
            SomeOver(F.Id("l"), Arrow(F.Id("Inp"), Reals(), Bools()),
                SomeOver(Sub("p", "B"), Arrow(F.Id("Inp"), Bools(), Reals(), Out(), Reals()), AndAll(
                    All("X", F.Id("Inp"), Call("IsResponse", new Formula.Apply(Sub("p", "A"), [X]))),
                    All("X", F.Id("Inp"), Call("Measurable", new Formula.Apply(F.Id("l"), [X]))),
                    All("Y", F.Id("Inp"), All("m", Bools(),
                        Call("IsResponse", new Formula.Apply(Sub("p", "B"), [Y, m])))),
                    behaviour))));
        return Disp(Iff(Call("IsOneBitAB", F.Id("d"), F.Id("P")), ProbabilityPrefix(body)));
    }

    private static Formula OneBitBaFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), A = F.Id("A"), B = F.Id("B"), t = F.Id("t"), m = F.Id("m");
        Formula lYt = new Formula.Apply(F.Id("l"), [Y, t]);
        Formula integral = Integral(Times2(Resp("A", X, lYt, t, A), Resp("B", Y, t, B)));
        Formula behaviour = All("X", F.Id("Inp"), All("Y", F.Id("Inp"), All("A", Out(), All("B", Out(),
            Equal(new Formula.Apply(F.Id("P"), [X, Y, A, B]), integral)))));
        Formula body = SomeOver(Sub("p", "A"), Arrow(F.Id("Inp"), Bools(), Reals(), Out(), Reals()),
            SomeOver(F.Id("l"), Arrow(F.Id("Inp"), Reals(), Bools()),
                SomeOver(Sub("p", "B"), Arrow(F.Id("Inp"), Reals(), Out(), Reals()), AndAll(
                    All("X", F.Id("Inp"), All("m", Bools(),
                        Call("IsResponse", new Formula.Apply(Sub("p", "A"), [X, m])))),
                    All("Y", F.Id("Inp"), Call("Measurable", new Formula.Apply(F.Id("l"), [Y]))),
                    All("Y", F.Id("Inp"), Call("IsResponse", new Formula.Apply(Sub("p", "B"), [Y]))),
                    behaviour))));
        return Disp(Iff(Call("IsOneBitBA", F.Id("d"), F.Id("P")), ProbabilityPrefix(body)));
    }

    private static Formula InputSetFormula(string name, (byte, byte)[] pairs)
    {
        var items = new List<Formula> { OpenBrace };
        for (var index = 0; index < pairs.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(Pair(pairs[index].Item1, pairs[index].Item2));
        }
        items.Add(CloseBrace);
        return Disp(Equal(F.Id(name), Seq([.. items])));
    }

    private static Formula ClaimFormula()
    {
        Formula v = F.Id("v"), P = F.Id("P"), d = F.Id("d"), univ = F.Id("univ");
        Formula values(string cls, Formula xs, Formula ys) =>
            Seq(OpenBrace, v, Sp, Mid, Sp, Some("P", Arrow(F.Id("Inp"), F.Id("Inp"), Out(), Out(), Reals()),
                AndAll(Call(cls, d, P), Equal(Call("bell", xs, ys, P), v))), CloseBrace);
        Formula greatest(string cls, Formula xs, Formula ys, byte[] bound) =>
            Call("IsGreatest", values(cls, xs, ys), D(bound));
        Formula body = AndAll(
            greatest("IsOneBitAB", univ, univ, [1, 2]),
            greatest("IsOneBitBA", univ, univ, [1, 2]),
            greatest("IsLocal", F.Id("symInputs"), F.Id("symInputs"), [7]),
            greatest("IsLocal", F.Id("symInputs"), F.Id("asymInputs"), [4]));
        Formula quantified = All("d", Seq(Mathbb, Grp(F.Id("N"))),
            Implies(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, d), body));
        return Disp(Iff(F.Id("claim"), quantified));
    }
}
