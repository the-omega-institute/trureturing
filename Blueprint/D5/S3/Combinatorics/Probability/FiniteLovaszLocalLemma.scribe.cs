using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class FiniteLovaszLocalLemmaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of rare dependent events can be avoided simultaneously under the exponential symmetric local-lemma criterion.",
        H("The Finite Symmetric Lovasz Local Lemma"),
        Blocks(
            Paragraph(Text(
                "Let Omega and I be finite types, with decidable equality on I. A real weight w "
                + "on Omega is nonnegative and sums to one. For a set E, write P(E) for the sum "
                + "of w over E. Let A_i be the bad events and G a simple graph on I with "
                + "decidable adjacency. JointIndependence(w,A,G) means that for every index i "
                + "and finite set S disjoint from i and all its neighbors, the probability of "
                + "A_i intersected with all A_j for j in S equals P(A_i) times the probability "
                + "of the latter intersection. Pairwise independence alone is insufficient.")),
            Describe.Lean(DescribeId.Create("symmetric-finite"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Probability/FiniteLovaszLocalLemma.lovasz_local_lemma_symmetric_finite"),
                H("Positive Probability of Avoiding Every Bad Event"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/atlas2026finitelovasz")),
                Blocks(Paragraph(Text(
                    "For a nonnegative real p and natural d, suppose every bad event has "
                    + "probability at most p, the maximum degree of G is at most d, and the "
                    + "stated joint independence condition holds. If exp(1) p (d+1) is at most "
                    + "one, the event that all bad events fail has strictly positive probability. "
                    + "The conclusion includes the zero-degree boundary case. It asserts "
                    + "simultaneous avoidance and does not provide an efficient search algorithm."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var o = F.Id("Omega"); var i = F.Id("I"); var w = F.Id("w"); var a = F.Id("A");
        var g = F.Id("G"); var p = F.Id("p"); var d = F.Id("d"); var x = F.Id("x");
        var premises = And(Call("NonnegativeWeights", w), Eq(Call("TotalWeight", w), D(1)),
            Le(D(0), p), Le(Call("maxDegree", g), d),
            All("x", i, Le(Call("P", w, Call("Apply", a, x)), p)),
            Call("JointIndependence", w, a, g),
            Le(Mul(Mul(Call("exp", D(1)), p), Add(Call("RealCast", d), D(1))), D(1)));
        return Disp(All("Omega", Call("Type"), Instance("Fintype", o,
            All("I", Call("Type"), Instance("Fintype", i, Instance("DecidableEq", i,
            All("w", Call("Function", o, Call("Real")),
            All("A", Call("Function", i, Call("Set", o)), All("G", Call("SimpleGraph", i),
            Instance("DecidableRel", Call("Adj", g), All("p", Call("Real"), All("d", Call("Nat"),
            Implies(premises, Lt(D(0), Call("P", w, Call("AvoidAll", a))))))))))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
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
