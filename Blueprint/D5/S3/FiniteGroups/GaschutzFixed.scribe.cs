using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class GaschutzFixedDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef NikolovSegal =
        LibraryNoteRef.Create("D5/L/FiniteGroups/nikolov2011powers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quotient-generating ordered tuple can be corrected inside a normal subgroup "
        + "to generate any finite group while keeping an arbitrary set fixed.",
        H("Gaschutz Lifting with an Arbitrary Fixed Set"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-set-gaschutz-lifting"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GaschutzFixed.gaschutz_fixed"),
                H("Lifting an ordered tuple"),
                StatementSource.FromAuthor(LiftingStatement()),
                AssessedProvenance.FromLiterature(NikolovSegal),
                Blocks(
                    Paragraph(Text(
                        "G is any finite group in any universe, N is a normal subgroup, X is "
                        + "any subset, and y is an ordered tuple indexed by Fin(n). The closure "
                        + "notation denotes the generated subgroup, top is the whole group, "
                        + "and join is the subgroup join. The hypothesis hgen asks for an "
                        + "ordered tuple z of the same length generating G. The hypothesis "
                        + "hquot says that N together with X and y generates G.")),
                    Paragraph(Text(
                        "There is an ordered tuple a of elements of N for which X and the "
                        + "products a(i)y(i) generate G. These are left corrections and the "
                        + "set X stays fixed. The statement includes zero-length tuples, "
                        + "and imposes no commutativity, solvability or Frattini condition.")),
                    Paragraph(Text(
                        "In the displayed formulas, Tuple(n,H) is the function type from "
                        + "Fin(n) to H, and leftCorrect(a,y) is the tuple with coordinate "
                        + "a(i)y(i), using the inclusion of N in G. The symbol goodCorrections "
                        + "denotes the finite set of tuples a in Tuple(n,N) whose corrected "
                        + "coordinates generate G together with X.")),
                    Paragraph(Text(
                        "For a subgroup H containing X, a correction can place all coordinates "
                        + "in H only when the join of N and H is G. In that case normality "
                        + "gives a point in every correction fiber, and translation identifies "
                        + "each fiber with the intersection of N and H. The constrained count "
                        + "is therefore the size of that intersection raised to n.")),
                    Paragraph(Text(
                        "A corrected tuple generates together with X exactly when it avoids "
                        + "every proper subgroup containing X. Inclusion-exclusion expresses "
                        + "the number of these tuples through the constrained intersection "
                        + "counts. Each constrained intersection count depends only on N, "
                        + "the intersection subgroup, and n, and is independent of y; "
                        + "therefore the total number of generating corrections depends "
                        + "only on G, N, X, and n. The "
                        + "generating tuple z has the identity correction, giving positivity "
                        + "and hence the required correction for y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaschutz-correction-count-invariance"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/GaschutzFixed.good_correction_card_eq"),
                H("The generating-correction count is invariant"),
                StatementSource.FromAuthor(CountStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two tuples of the same length satisfying the quotient-generation "
                    + "hypothesis with the same N and X, the finite sets of generating "
                    + "corrections have equal cardinality. Mathlib's finite inclusion-exclusion "
                    + "identity applies also to the empty intersection, so the argument "
                    + "does not exclude n equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-generator-tuple-rank-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/GaschutzFixed.tuple_generation_iff_rank_le"),
                H("Tuple generation and generator rank"),
                StatementSource.FromAuthor(RankStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An ordered n-tuple generates G exactly when Group.rank(G) is at most n. "
                    + "One direction bounds the cardinality of the tuple's image. For the "
                    + "other, enumerate a minimum generating set, place its entries in the "
                    + "first positions of Fin(n), and fill unused positions with the identity. "
                    + "The construction works even when both the minimum set and Fin(n) "
                    + "are empty. This equivalence gives the rank hypothesis of the "
                    + "Nikolov-Segal formulation without adding a positive-length premise."))),
                DescribeRole.Theorem))));

    private static Formula LiftingStatement()
    {
        var g = F.Id("G");
        var n = F.Id("n");
        var kernel = F.Id("N");
        var x = F.Id("X");
        var y = F.Id("y");
        var z = F.Id("z");
        var a = F.Id("a");
        var tuple = Call("Tuple", n, g);
        var hgen = ExistsIn("z", tuple, Equal(Call("closure", Call("range", z)), Top));
        var hquot = Equal(Call("join", kernel,
            Call("closure", Call("union", x, Call("range", y)))), Top);
        var conclusion = ExistsIn("a", Call("Tuple", n, kernel),
            Equal(Call("closure", Call("union", x, Call("range", Call("leftCorrect", a, y)))), Top));
        Formula body = Implies(And(hgen, hquot), conclusion);
        body = All("y", tuple, body);
        body = All("X", Call("Set", g), body);
        body = All("N", Call("Subgroup", g), Implies(Call("Normal", kernel), body));
        body = All("n", F.Id("Nat"), body);
        return Disp(All("G", F.Id("Typeu"),
            Implies(And(Call("Group", g), Call("Finite", g)), body)));
    }

    private static Formula CountStatement()
    {
        var g = F.Id("G");
        var n = F.Id("n");
        var kernel = F.Id("N");
        var x = F.Id("X");
        var y = F.Id("y");
        var z = F.Id("z");
        var tuple = Call("Tuple", n, g);
        Formula QuotientGeneration(Formula t) => Equal(Call("join", kernel,
            Call("closure", Call("union", x, Call("range", t)))), Top);
        Formula body = Implies(And(QuotientGeneration(y), QuotientGeneration(z)),
            Equal(Call("card", Call("goodCorrections", kernel, x, y)),
                Call("card", Call("goodCorrections", kernel, x, z))));
        body = All("z", tuple, body);
        body = All("y", tuple, body);
        body = All("X", Call("Set", g), body);
        body = All("N", Call("Subgroup", g), Implies(Call("Normal", kernel), body));
        body = All("n", F.Id("Nat"), body);
        return Disp(All("G", F.Id("Typeu"),
            Implies(And(Call("Group", g), Call("Fintype", g)), body)));
    }

    private static Formula RankStatement()
    {
        var g = F.Id("G");
        var n = F.Id("n");
        var z = F.Id("z");
        Formula body = new Formula.Logic(
            ExistsIn("z", Call("Tuple", n, g), Equal(Call("closure", Call("range", z)), Top)),
            FormulaLogicOperator.Iff,
            new Formula.Relation(Call("rank", g), FormulaRelationOperator.LessThanOrEqual, n));
        body = All("n", F.Id("Nat"), body);
        return Disp(All("G", F.Id("Typeu"),
            Implies(And(Call("Group", g), Call("Finite", g)), body)));
    }

    private static Formula Top => F.Id("top");
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula next in rest)
            result = new Formula.Logic(result, FormulaLogicOperator.And, next);
        return result;
    }
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula ExistsIn(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
}
