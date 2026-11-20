using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Recurrence;

internal sealed class VasilyevForceDivergenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/vasilyev2026upordown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There is a set of positive integers that forces divergence in every superset but contains no all-up tail.",
        H("Vasilyev's force-divergence question"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vasilyev-positive-vertices"),
                DeclarationHandle.Create(Module + ".P"),
                H("Positive vertices"),
                StatementSource.FromAuthor(Disp(PositiveVertices())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The positive integers are the vertices of Vasilyev's up-down graph."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-up-step"),
                DeclarationHandle.Create(Module + ".U"),
                H("Up step"),
                StatementSource.FromAuthor(Disp(UpStep())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The map takes natural numbers to natural numbers and div denotes Nat.div. "
                    + "On positive vertices this gives the ceiling of 3x/2 in Definition 1.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-down-step"),
                DeclarationHandle.Create(Module + ".D"),
                H("Down step"),
                StatementSource.FromAuthor(Disp(DownStep())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The map takes natural numbers to natural numbers and div denotes Nat.div. "
                    + "On positive vertices this gives the ceiling of x/2 in Definition 1.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-set-step"),
                DeclarationHandle.Create(Module + ".T"),
                H("Step for a chosen set"),
                StatementSource.FromAuthor(Disp(SetStep())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Definition 1.1 selects the up or down map by membership in the chosen set. "
                    + "Lean uses classical decidability for this choice and defines a natural-to-natural map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-force-divergent"),
                DeclarationHandle.Create(Module + ".ForceDivergent"),
                H("Force-divergence"),
                StatementSource.FromAuthor(Disp(PredicateDefinition("ForceDivergent", ForceBody(F.Id("A"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 2.3 quantifies over all supersets in the positive integers. "
                    + "The witness starts in P and its orbit avoids Mathlib's Function.periodicPts "
                    + "at every natural time. This set consists of the points with a positive period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-contains-tail"),
                DeclarationHandle.Create(Module + ".ContainsTail"),
                H("Contains an all-up tail"),
                StatementSource.FromAuthor(Disp(PredicateDefinition("ContainsTail", TailBody(F.Id("A"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 3.2 describes the chain tail starting at a positive vertex. "
                    + "The forward up orbit includes that vertex at time zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-force-divergence-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Question 7.7"),
                StatementSource.FromAuthor(Disp(
                    new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Vasilyev, Question 7.7 (printed p. 33).")),
                    Paragraph(
                        Text("“Does every force-divergent set, that is, every "),
                        Math(F.Id("A")),
                        Text(" such that "),
                        Math(new Formula.Subscript(F.Id("T"), F.Id("S"))),
                        Text(" is unbounded for all "),
                        Math(F.Id("S")),
                        Text(" ⊇ "),
                        Math(F.Id("A")),
                        Text(", contain a tail of a chain?”")),
                    Paragraph(Text(
                        "Let P be the positive integers. At x in P the up and down steps are the "
                        + "ceilings of 3x/2 and x/2, respectively. Lean writes them as (3x + 1) div 2 "
                        + "and (x + 1) div 2 with natural-number division. The map T(S) takes "
                        + "the up step at members of S and the down step elsewhere.")),
                    Paragraph(Text(
                        "A subset A of P is force-divergent if, for every S with A contained in S "
                        + "and S contained in P, some positive starting vertex has an orbit under T "
                        + "that never enters a periodic cycle. Here iterate(f, t, x) applies f to x "
                        + "exactly t times, and periodicPts(f) is the set of points of positive period. "
                        + "A contains a tail if the whole forward up orbit of some positive vertex "
                        + "lies in A, including time zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vasilyev-force-divergence-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A force-divergent set without a chain tail"),
                StatementSource.FromAuthor(Disp(new Formula.Not(ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Start with b(0) = 3. Define b(n + 1) to be the 2b(n)-th up iterate of n + 1. "
                        + "Omit exactly the values b(n + 1) from P to obtain A. Each positive vertex "
                        + "n + 1 then has an up iterate outside A.")),
                    Paragraph(Text(
                        "Each up step increases a positive value by at least one, so b(n + 1) > 2b(n). "
                        + "For m = b(n + 1), the ceiling bounds put both D(m) and U(D(m)) strictly "
                        + "between b(n) and m. The gap contains no omitted value. Thus, for any superset "
                        + "S, an orbit at a positive vertex in S grows after one up step. At a vertex "
                        + "outside S, that vertex is an omitted m and its next three steps are down, up, up. "
                        + "The endpoint is at least 9m/8, which exceeds m.")),
                    Paragraph(Text(
                        "Concatenating these blocks gives unbounded orbit values from every positive start "
                        + "under each allowed S. An eventually periodic orbit has only finitely many "
                        + "values. The same A therefore forces divergence and excludes every all-up tail."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula NaturalSets => Call("Set", Naturals);

    private static Formula PositiveVertices()
    {
        Formula x = F.Id("x");
        return Equal(F.Id("P"), Seq(OpenBrace, x, Sp, Colon, Sp, Naturals, Sp, Mid, Sp,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x), CloseBrace));
    }

    private static Formula UpStep()
    {
        Formula x = F.Id("x");
        return Bind(FormulaQuantifier.ForAll, "x", Naturals,
            Equal(Call("U", x), DivideByTwo(Add(Multiply(D(3), x), D(1)))));
    }

    private static Formula DownStep()
    {
        Formula x = F.Id("x");
        return Bind(FormulaQuantifier.ForAll, "x", Naturals,
            Equal(Call("D", x), DivideByTwo(Add(x, D(1)))));
    }

    private static Formula DivideByTwo(Formula numerator) =>
        Call("div", numerator, D(2));

    private static Formula SetStep()
    {
        Formula s = F.Id("S"), x = F.Id("x");
        Formula member = Member(x, s);
        Formula cases = Seq(Begin, Grp(F.Id("cases")),
            Call("U", x), Amp, member, RowBreak,
            Call("D", x), Amp, Neg, Sp, Parenthesized(member),
            End, Grp(F.Id("cases")));
        return Bind(FormulaQuantifier.ForAll, "S", NaturalSets,
            Bind(FormulaQuantifier.ForAll, "x", Naturals,
                Equal(new Formula.Apply(Call("T", s), [x]), cases)));
    }

    private static Formula PredicateDefinition(string name, Formula body) =>
        Bind(FormulaQuantifier.ForAll, "A", NaturalSets,
            new Formula.Logic(Call(name, F.Id("A")), FormulaLogicOperator.Iff, body));

    private static Formula ForceBody(Formula a)
    {
        Formula s = F.Id("S"), x = F.Id("x"), t = F.Id("t"), positive = F.Id("P");
        Formula step = Call("T", s);
        Formula entersCycle = Bind(FormulaQuantifier.Exists, "t", Naturals,
            Member(Call("iterate", step, t, x), Call("periodicPts", step)));
        Formula divergentStart = Bind(FormulaQuantifier.Exists, "x", Naturals,
            new Formula.Logic(Member(x, positive), FormulaLogicOperator.And,
                new Formula.Not(entersCycle)));
        return Bind(FormulaQuantifier.ForAll, "S", NaturalSets,
            Implies(SubsetOf(s, positive), Implies(SubsetOf(a, s), divergentStart)));
    }

    private static Formula TailBody(Formula a)
    {
        Formula y = F.Id("y"), k = F.Id("k");
        return Bind(FormulaQuantifier.Exists, "y", Naturals,
            new Formula.Logic(Member(y, F.Id("P")), FormulaLogicOperator.And,
                Bind(FormulaQuantifier.ForAll, "k", Naturals,
                    Member(Call("iterate", F.Id("U"), k, y), a))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A");
        return Bind(FormulaQuantifier.ForAll, "A", NaturalSets,
            Implies(SubsetOf(a, F.Id("P")), Implies(ForceBody(a), TailBody(a))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);

    private static Formula SubsetOf(Formula subset, Formula superset) =>
        new Formula.Relation(subset, FormulaRelationOperator.SubsetOf, superset);
}
