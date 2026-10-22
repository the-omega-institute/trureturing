using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ComponentPacking;

internal sealed class AhanjidehEkimYildizZDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/ahanjidehekimyildiz2022matching");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least matching number of an almost regular, triangle-free, factor-critical graph has an exact formula for every odd degree at least twenty-one.",
        H("The extremal matching number for odd degrees"),
        Blocks(
            Node("z", "The least admissible matching number", ZFormula(),
                "Definition 4.2, page 8: “For any d ≥ 2, let Z(d) be the smallest natural number n such that there exists a d-regular (if d is even) or almost d-regular (if d is odd) triangle-free and factor-critical graph G with ν(G) = n.” Finite graphs have carrier Fin n. The matching number is DimerVirialFourthDifferenceRefutation.matchingNumber; the minimum is the infimum in the natural numbers. The formula defines Z for every natural d, and the theorem uses only odd d at least 21.",
                "Z", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 6.5", Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                "Conjecture 6.5, page 20: “For d ≥ 21 and odd, we have Z(d) = ⌊5(d + 1)/4⌋.” The natural-number quotient is floor division. The degree d ranges over all natural numbers satisfying both hypotheses.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjectured equality", Disp(ClaimBody()),
                "A triangle-free graph below the proposed extremal order admits a pentagon partition through the three-eighths minimum-degree theorem. The exceptional degree 23 and order 59 is handled by deleting the deficient vertex and extending the partition. The cyclic missing-edge incidence inequalities rule out total slack one and three. The almost regular pentagon constructions attain the remaining matching number.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("aeyz-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula v, Formula type, Formula body) =>
        Seq(Exists, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Graph(Formula n) => Call("SimpleGraph", Call("Fin", n));
    private static Formula Quotient(Formula d) => new Formula.Apply(Seq(Named("Nat"), Dot, Named("div")), [Mul(D(5), Parenthesized(Add(d, D(1)))), D(4)]);

    private static Formula ClaimBody()
    {
        Formula d = F.Id("d");
        return All(d, N, Logic(Rel(D(2, 1), FormulaRelationOperator.LessThanOrEqual, d),
            FormulaLogicOperator.Implies, Logic(Call("Odd", d), FormulaLogicOperator.Implies,
                Rel(Call("Z", d), FormulaRelationOperator.Equal, Quotient(d)))));
    }

    private static Formula ZFormula()
    {
        Formula d = F.Id("d"), m = F.Id("m"), n = F.Id("n"), g = F.Id("G");
        Formula regular = Call("ite", Call("Even", d), Call("IsRegularOfDegree", g, d),
            Call("IsAlmostRegular", g, d));
        Formula properties = Logic(regular, FormulaLogicOperator.And,
            Logic(Call("CliqueFree", g, D(3)), FormulaLogicOperator.And,
                Logic(Call("IsFactorCritical", g), FormulaLogicOperator.And,
                    Rel(Call("matchingNumber", g), FormulaRelationOperator.Equal, m))));
        Formula graphs = Some(n, N, Some(g, Graph(n), properties));
        Formula set = Seq(Esc, OpenBrace, m, Colon, Sp, N, Sp, Mid, Sp, graphs, Esc, CloseBrace);
        return Disp(All(d, N, Rel(Call("Z", d), FormulaRelationOperator.Equal, Call("sInf", set))));
    }
}
