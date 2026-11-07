using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class OddPowerSelfConjugateCMPDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/dietzflowerslockard2026cmp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dietz–Flowers–Lockard Question 5.14 has a universal negative answer.",
        H("Odd powers cannot be self-conjugate CMP sizes"),
        Blocks(
            Node("ismary", "m-ary partition", "IsMAry", IsMAryFormula(),
                "Definition 1.1(2), printed page 386: “If all of the parts of λ are powers of m, then we say λ is m-ary.” Here the positive row lengths of the YoungDiagram μ are the parts and the exponents are natural numbers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("multiplicity", "Part multiplicity", "multiplicity", MultiplicityFormula(),
                "Definition 1.1(2), printed page 386: “Let a_i denote the number of times that the part m^i appears in λ.” The list count is taken over the row lengths.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("iscmp", "Conjugate m-ary partition", "IsCMP", IsCMPFormula(),
                "Definition 1.1(3), printed page 386: “If λ and λ' are both m-ary, then λ is a conjugate m-ary partition (or CMP).” The conjugate is YoungDiagram.transpose.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question 5.14", "claim", Equal(Call("claim"), ClaimBody()),
                "Question 5.14, printed page 404: “When m is odd, are there any self-conjugate CMPs of odd powers of m?” The displayed proposition is its negative answer, with m ≥ 2, Odd m, exponent 2s+1, literal YoungDiagram equality for self-conjugacy, and the two m-ary conditions.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Negative answer", "result", ClaimBody(),
                "The finite row fibers are differences of adjacent column-height ranges. The m-ary hypotheses make every positive row and column height congruent to 1 modulo m−1; self-conjugacy identifies the largest row and column. Summing the fibers gives (m−1)^2 dividing N−(2L−1), then oddness gives 2(m−1) dividing N−1. For N=m^(2s+1), the same divisor also divides N−m, forcing it to divide m−1, which contradicts m ≥ 2.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("dfl514-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Diagram() => Named("YoungDiagram");
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Par(body));
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, Par(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Neq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula RowLen(Formula mu, Formula i) => Call("rowLen", mu, i);
    private static Formula RowLens(Formula mu) => Call("rowLens", mu);
    private static Formula Transpose(Formula mu) => Call("transpose", mu);
    private static Formula Card(Formula mu) => Call("card", mu);

    private static Formula IsMAryBody(Formula m, Formula mu) =>
        Forall("i", Naturals(), Imp(Lt(new Formula.Number(0), RowLen(mu, F.Id("i"))),
            Exists("j", Naturals(), Eq(RowLen(mu, F.Id("i")), Pow(m, F.Id("j"))))));

    private static Formula IsMAryFormula() =>
        Forall("m", Naturals(), Forall("mu", Diagram(),
            Eq(Call("IsMAry", F.Id("m"), F.Id("mu")), IsMAryBody(F.Id("m"), F.Id("mu")))));

    private static Formula MultiplicityFormula() =>
        Forall("m", Naturals(), Forall("mu", Diagram(), Forall("j", Naturals(),
            Eq(Call("multiplicity", F.Id("m"), F.Id("mu"), F.Id("j")),
                Call("count", RowLens(F.Id("mu")), Pow(F.Id("m"), F.Id("j")))))));

    private static Formula IsCMPFormula() =>
        Forall("m", Naturals(), Forall("mu", Diagram(),
            Eq(Call("IsCMP", F.Id("m"), F.Id("mu")),
                And(Call("IsMAry", F.Id("m"), F.Id("mu")),
                    Call("IsMAry", F.Id("m"), Transpose(F.Id("mu")))))));

    private static Formula ClaimBody()
    {
        Formula m = F.Id("m"), s = F.Id("s"), mu = F.Id("mu");
        Formula exponent = Add(Mul(new Formula.Number(2), s), new Formula.Number(1));
        Formula size = Eq(Card(mu), Pow(m, exponent));
        Formula cmp = Call("IsCMP", m, mu);
        return Forall("m", Naturals(), Imp(Leq(new Formula.Number(2), m), Imp(Call("Odd", m),
            Forall("s", Naturals(), Forall("mu", Diagram(),
                Imp(size, Imp(cmp, Neq(Transpose(mu), mu))))))));
    }
}
