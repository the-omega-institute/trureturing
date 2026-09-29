using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Sandpiles;

internal sealed class TorusColumnTopplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/arndt2017a293452");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the n x 1 torus, fill every cell except c[0,0] with 4 grains and topple cells holding at least 4 grains, the grains sent to c[0,0] being lost. For every n at least 2 the process reaches a final state, and every legal toppling sequence ending in a final state has A023855(n - 1) topplings, in whatever order the cells are chosen (OEIS A293452, with the printed index corrected).",
        H("The toppling count of the n x 1 torus sandpile is A023855(n - 1)"),
        Blocks(
            Node("cell", "The cells of the n x k torus", CellFormula(),
                "OEIS A249872: \"Let the lattice be c[i,j], 0 <= i,j < n.\" A293452 uses the n X k torus; the cell c[i,j] is the pair (i, j) of residues modulo n and k.",
                "Cell", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("initial", "The initial configuration", InitialFormula(),
                "OEIS A249872: \"Fill each cell except c[0,0] with 4 grains of sand.\"",
                "initial", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("neighbours", "The four neighbours on the torus", NeighboursFormula(),
                "The 4 neighbours of a cell on the torus, as a list; on the n x 1 torus the last two are the cell itself.",
                "neighbours", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("topple", "One iteration", ToppleFormula(),
                "OEIS A249872: \"Decrement the chosen cell by 4 and increment its 4 neighbors by 1. c[0,0] is never increased, sand grains placed here are lost.\" A neighbour occurring twice in the list receives two grains.",
                "topple", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("run", "The configuration after a toppling sequence", RunFormula(),
                "The cells of the list L are toppled in order, starting from the initial configuration.",
                "run", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("legal", "Legal toppling sequences", LegalFormula(),
                "OEIS A249872: \"Find a c[i,j] >= 4.\" Every cell of the sequence holds at least 4 grains when it is toppled.",
                "Legal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stable", "Final states", StableFormula(),
                "OEIS A249872: \"Until all c[i,j] < 4\".",
                "Stable", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a023855", "OEIS A023855", SequenceFormula(),
                "OEIS A023855: \"a(n) = 1*(n) + 2*(n-1) + 3*(n-2) + ... + (n+1-k)*k, where k = floor((n+1)/2).\"",
                "a023855", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of OEIS A293452, index corrected", ClaimDefinitionFormula(),
                "OEIS A293452, FORMULA: \"Conjecture: T(n,1) = A023855(n).\" The printed index is off by one: T(1,1) = 0 while A023855(1) = 1, and the column T(n,1) = 0, 1, 2, 7, 10, 22, ... of the entry is A023855 shifted by one place. The claim is the corrected identity T(n,1) = A023855(n - 1) for n at least 2, with T(n,1) the length of every legal toppling sequence that ends in a final state (\"According to Knuth, it does not matter which cell is chosen\"), together with the existence of such a sequence.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Least action and the discrete maximum principle", ClaimFormula(),
                "Write v(i) for the number of topplings of the cell (i, 0) in a legal sequence. Each toppling of (i, 0) removes 4 grains and returns 2 through the two self-neighbours, so every cell (i, 0) other than c[0,0] holds 4 - 2 v(i) + v(i - 1) + v(i + 1) grains, and the cell c[0,0] is never toppled. Let u(x) = (x(n - x) + [n even] min(x, n - x)) / 2 for 0 <= x <= n; its final configuration 4 - 2 u(x) + u(x - 1) + u(x + 1) is 3 at every cell other than c[0,0] (1 <= x < n), except 2 at x = n/2 when n is even. Least action: along a legal sequence v stays below u, because a cell with v(x) = u(x) holds at most 3 grains and cannot be toppled; hence every legal sequence has at most the sum of u topplings, and a sequence of maximal length ends in a final state. Maximum principle: if a legal sequence ends in a final state, the defect d = u - v is nonnegative, vanishes at x = 0 and x = n, and satisfies d(x - 1) + d(x + 1) - 2 d(x) >= 0 except >= -1 at x = n/2; at the leftmost and the rightmost maximum of d these inequalities fail unless d = 0. So every such sequence has the sum of u topplings, which is the sum over 1 <= j <= floor(n/2) of j (n - j), that is A023855(n - 1).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arndt-2017-a293452-torus-column-sandpile"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("torus-sandpile-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula Cells(Formula n, Formula k) => Call("Cell", n, k);
    private static Formula Lists(Formula n) => Call("List", Cells(n, D(1)));

    private static Formula CellFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All("n", Naturals(), All("k", Naturals(),
            Equal(Cells(n, k), Seq(Call("ZMod", n), Sp, Times, Sp, Call("ZMod", k))))));
    }

    private static Formula InitialFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), q = F.Id("q");
        return Disp(All("q", Cells(n, k),
            Equal(Call("initial", n, k, q), Call("ite", Equal(q, D(0)), D(0), D(4)))));
    }

    private static Formula NeighboursFormula()
    {
        Formula p = F.Id("p");
        Formula p1 = Sub(p, D(1)), p2 = Sub(p, D(2));
        Formula list = Seq(OpenBracket, Pair(Add(p1, D(1)), p2), Comma, Sp, Pair(Subtract(p1, D(1)), p2),
            Comma, Sp, Pair(p1, Add(p2, D(1))), Comma, Sp, Pair(p1, Subtract(p2, D(1))), CloseBracket);
        return Disp(Equal(Call("neighbours", p), list));
    }

    private static Formula ToppleFormula()
    {
        Formula c = F.Id("c"), p = F.Id("p"), q = F.Id("q");
        Formula value = Add(Subtract(new Formula.Apply(c, [q]), Call("ite", Equal(q, p), D(4), D(0))),
            Call("ite", Equal(q, D(0)), D(0), Call("count", q, Call("neighbours", p))));
        return Disp(Equal(Call("topple", c, p, q), value));
    }

    private static Formula RunFormula()
    {
        Formula L = F.Id("L"), n = F.Id("n"), k = F.Id("k");
        return Disp(Equal(Call("run", L), Call("foldl", Named("topple"), Call("initial", n, k), L)));
    }

    private static Formula LegalFormula()
    {
        Formula L = F.Id("L"), i = F.Id("i");
        Formula body = Implies(Less(i, Call("length", L)),
            AtMost(D(4), new Formula.Apply(Call("run", Call("take", i, L)), [Sub(L, i)])));
        return Disp(Iff(Call("Legal", L), All("i", Naturals(), body)));
    }

    private static Formula StableFormula()
    {
        Formula c = F.Id("c"), q = F.Id("q");
        return Disp(Iff(Call("Stable", c), Seq(Forall, Sp, q, Comma, Sp, Less(new Formula.Apply(c, [q]), D(4)))));
    }

    private static Formula SequenceFormula()
    {
        Formula m = F.Id("m"), j = F.Id("j");
        Formula range = Call("Icc", D(1), Call("NatDiv", Add(m, D(1)), D(2)));
        Formula sum = Seq(Sum, Underscore, Grp(Member(j, range)), Sp,
            Mul(j, Parenthesized(Subtract(Add(m, D(1)), j))));
        return Disp(All("m", Naturals(), Equal(Call("a023855", m), sum)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), L = F.Id("L");
        Formula final = And(Call("Legal", L), Call("Stable", Call("run", L)));
        Formula exists = Some("L", Lists(n), final);
        Formula every = All("L", Lists(n), Implies(Call("Legal", L), Implies(Call("Stable", Call("run", L)),
            Equal(Call("length", L), Call("a023855", Subtract(n, D(1)))))));
        return All("n", Naturals(), Implies(AtMost(D(2), n), And(exists, every)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(F.Id("claim"));
}
