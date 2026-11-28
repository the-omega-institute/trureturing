using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class BojicThreeTermDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm.piecewise_trinomial_interface";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/bojic2026semisimple");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-distinct-offset cyclic branch has an explicit local unipotent valuation and order.",
        H("Three-distinct-offset cyclic local order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bojic-three-term-cyclic-interface"),
                DeclarationHandle.Create(Result),
                H("The explicit local valuation and order"),
                StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let q be odd and let the three distinct exponents lie in the cyclic "
                        + "window of length 2^m q. The polynomial is the trinomial "
                        + "X^a + X^b + X^c over F2. For a monic irreducible factor f of "
                        + "X^q − 1 that does not divide this trinomial, the local quotient "
                        + "of thickness 2^m has a unique semisimple factor.")),
                    Paragraph(Text(
                        "The dyadic case split in preregisteredDegree gives the first positive "
                        + "Taylor degree after removing the common power of two from the "
                        + "three offsets. The valuation of the unipotent factor minus one "
                        + "is the minimum of this degree and 2^m.")),
                    Paragraph(Text(
                        "The unipotent factor has the least power-of-two order p satisfying "
                        + "2^m ≤ preregisteredDegree · p. The semisimple factor and the "
                        + "unipotent factor multiply to the actual class in the primary "
                        + "quotient.")),
                    Paragraph(Text(
                        "This settles the cyclic three-term direction in Section 11 for the "
                        + "stated distinct-offset range. Rules on other graphs are outside "
                        + "the statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bojic-2026-three-term-cyclic-unipotent-order"),
                    ResolutionKind.Proved)))));

    private static Formula MainFormula()
    {
        Formula q = F.Id("q"), m = F.Id("m"), a = F.Id("a"), b = F.Id("b");
        Formula c = F.Id("c"), f = F.Id("f"), s = F.Id("s"), v = F.Id("v");
        Formula n = F.Id("n"), k = F.Id("k"), p = F.Id("p");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula poly = Call("Polynomial", Call("ZMod", D(2)));
        Func<Formula, Formula, Formula> local = (x, y) => Call("Local", x, y);
        Func<Formula, Formula, Formula> pow = (x, y) => Seq(x, Caret, Grp(y));
        Func<Formula, Formula> cycle = x => Call("cycle", x);
        Func<Formula, Formula, Formula, Formula> tri = (x, y, z) => Call("trinomial", x, y, z);
        Func<Formula, Formula, Formula> project = (x, y) => Call("project", x, y);
        Formula primary = pow(F.Id("f"), pow(D(2), m));
        Formula g = project(primary, tri(a, b, c));
        Func<Formula, Formula> semi = x => Call("IsSemisimplePart", g, x);
        Formula unipotent = project(primary, v);
        Formula first = Call("preregisteredDegree", f, a, b, c);
        Formula decomposition = And(
            Exists("s", local(f, m), And(
                semi(s),
                All("t", local(f, m), Imp(semi(F.Id("t")), Equal(F.Id("t"), s))))),
            All("s", local(f, m), All("v", poly,
                Imp(semi(s), Imp(
                    Equal(g, Multiply(s, Add(Num(1), unipotent))),
                    And(
                        All("n", nat, Iff(
                            Rel(n, FormulaRelationOperator.LessThanOrEqual,
                                Call("min", first, pow(D(2), m))),
                            And(
                                Rel(n, FormulaRelationOperator.LessThanOrEqual, pow(D(2), m)),
                                Rel(pow(f, n), FormulaRelationOperator.Divides, v)))),
                        Call("IsLeast",
                            SetOf("p", nat, And(
                                Exists("k", nat, Equal(p, pow(D(2), k))),
                                Rel(Multiply(first, p), FormulaRelationOperator.GreaterThanOrEqual,
                                    pow(D(2), m)))),
                            Call("orderOf", Add(Num(1), unipotent)))))))));
        Formula result = decomposition;
        Formula[] premises = {
            Call("Odd", q),
            Rel(a, FormulaRelationOperator.LessThan, Multiply(pow(D(2), m), q)),
            Rel(b, FormulaRelationOperator.LessThan, Multiply(pow(D(2), m), q)),
            Rel(c, FormulaRelationOperator.LessThan, Multiply(pow(D(2), m), q)),
            Rel(a, FormulaRelationOperator.NotEqual, b),
            Rel(a, FormulaRelationOperator.NotEqual, c),
            Rel(b, FormulaRelationOperator.NotEqual, c),
            Call("Monic", f),
            Call("Irreducible", f),
            Rel(f, FormulaRelationOperator.Divides, cycle(q)),
            new Formula.Not(Rel(f, FormulaRelationOperator.Divides, tri(a, b, c)))
        };
        for (var i = premises.Length - 1; i >= 0; --i)
            result = Imp(premises[i], result);
        return All("q", nat, All("m", nat, All("a", nat, All("b", nat,
            All("c", nat, All("f", poly, result))))));
    }

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula SetOf(string name, Formula type, Formula body) =>
        Call("SetOf", All(name, type, body));
}
