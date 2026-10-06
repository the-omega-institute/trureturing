using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class UniformPolychromaticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite hyperedges with sufficiently many vertices and bounded intersection degree admit one coloring containing every color on every edge.",
        H("Polychromatic Coloring from Uniform Independent Colors"),
        Blocks(
            Paragraph(Text(
                "Let V be a finite vertex type and I a finite index type, both with decidable "
                + "equality. The function E assigns a finite vertex set to each index. "
                + "IntersectionDegree(E,i) counts indices j different from i whose vertex sets "
                + "intersect E_i. The edges need not have equal size or intersect in at most "
                + "one vertex; repeated vertex sets are allowed and are counted by their indices.")),
            Describe.Lean(DescribeId.Create("polychromatic-local-lemma"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Probability/UniformPolychromatic.finite_polychromatic_of_symmetric_LLL"),
                H("One Coloring Serves Every Hyperedge"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/erdoslovasz1975polychromatic")),
                Blocks(Paragraph(Text(
                    "For natural numbers L, s and D with L positive, assume each edge has at "
                    + "least s vertices and intersection degree at most D. If exp(1) L "
                    + "((L-1)/L)^s (D+1) is at most one, there is a function from V to Fin L "
                    + "whose restriction to each edge attains every color. All divisions and "
                    + "the displayed inequality are in the real numbers.")),
                    Paragraph(Text(
                    "Choose every vertex color independently and uniformly. A fixed color is "
                    + "absent from an edge with probability ((L-1)/L) raised to the edge size. "
                    + "Summing over colors bounds the bad-event probability. An edge's event "
                    + "depends only on its own vertex coordinates, while any conjunction of "
                    + "nonneighbor events depends only on the complementary coordinates. "
                    + "Product factorization gives the full dependency condition required by "
                    + "the symmetric local lemma. Its positive avoidance probability supplies "
                    + "a single coloring for the entire indexed family."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var v = F.Id("V"); var i = F.Id("I"); var e = F.Id("E"); var l = F.Id("L");
        var s = F.Id("s"); var d = F.Id("D"); var j = F.Id("i"); var c = F.Id("c");
        var color = F.Id("color"); var x = F.Id("v"); var lr = Call("RealCast", l);
        var fraction = Call("Divide", Call("Subtract", lr, D(1)), lr);
        var bound = Mul(Mul(Mul(Call("exp", D(1)), lr), Call("Pow", fraction, s)),
            Add(Call("RealCast", d), D(1)));
        var premises = And(Lt(D(0), l),
            All("i", i, Le(s, Call("Card", Call("Apply", e, j)))),
            All("i", i, Le(Call("IntersectionDegree", e, j), d)), Le(bound, D(1)));
        var conclusion = Exists("color", Call("Function", v, Call("Fin", l)),
            All("i", i, All("c", Call("Fin", l), Exists("v", v,
                And(Call("Mem", x, Call("Apply", e, j)), Eq(Call("Apply", color, x), c))))));
        return Disp(All("V", Call("Type"), Instance("Fintype", v, Instance("DecidableEq", v,
            All("I", Call("Type"), Instance("Fintype", i, Instance("DecidableEq", i,
            All("E", Call("Function", i, Call("Finset", v)), All("L", Call("Nat"),
            All("s", Call("Nat"), All("D", Call("Nat"), Implies(premises, conclusion))))))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var j = terms.Length - 2; j >= 0; --j)
            result = new Formula.Logic(terms[j], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}
