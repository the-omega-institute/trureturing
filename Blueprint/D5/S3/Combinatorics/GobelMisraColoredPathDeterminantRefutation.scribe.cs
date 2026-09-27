using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class GobelMisraColoredPathDeterminantRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/gobel2025colored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-vertex colored path pair refutes Conjecture 5.3 on determinant equality.",
        H("A Colored-Path Determinant Counterexample"),
        Blocks(
            Node("colored-path", "Labelled colored paths", "ColoredPath", ColoredPathFormula(),
                "A colored path on m vertices has a vertex-color function Fin(m) to V and an "
                    + "edge-color function Fin(m-1) to E. The distinct types V and E keep the "
                    + "vertex- and edge-color sets disjoint. A zero-based vertex index i "
                    + "represents the one-based position i.val+1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("concentration", "Generic concentration matrix", "concentration",
                ConcentrationFormula(),
                "For a colored path P, concentration(P) is a matrix over the integer "
                    + "multivariable polynomial ring on V+E. Its diagonal entry (i,i) is "
                    + "X(inl(vertexColor(P,i))). Its adjacent entries (i,i+1) and (i+1,i) "
                    + "are X(inr(edgeColor(P,i))); every other entry is zero. Thus equal "
                    + "colors produce equal matrix entries exactly as in color constraints "
                    + "(1)-(3) on printed page 5. The coefficients are integers, and the "
                    + "coefficient embedding from integers into reals is injective, so "
                    + "polynomial equality here is the same formal identity as over the reals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reflect", "Path reflection", "reflect", ReflectFormula(),
                "Reflection preserves color labels while reversing positions. On zero-based "
                    + "indices it sends a vertex index i to m-1-i.val and an edge index i to "
                    + "m-2-i.val. In one-based positions these are r to m+1-r for vertices "
                    + "and r to m-r for edges.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("config-thirty-six", "Theorem 3.6 configuration", "Config36",
                Config36Formula(),
                "Theorem 3.6 states the following clauses verbatim: “(1) lambda({p_i, "
                    + "p_{i+1}}) = lambda({q_i, q_{i+1}}) for every i in {1, 2, ..., m-1}, "
                    + "(2) lambda(p_1) = lambda(p_{2n+1}) and lambda(q_1) = "
                    + "lambda(q_{2n+1}) for every n in {1, 2, ..., m/2-1} (odd vertices have "
                    + "the same color), (3) lambda(p_2) = lambda(p_{2n}) and lambda(q_2) = "
                    + "lambda(q_{2n}) for every n in {1, 2, ..., m/2} (even vertices have "
                    + "the same color), (4) lambda(p_1) = lambda(q_2) and lambda(p_2) = "
                    + "lambda(q_1).” Config36 writes the monochromatic clauses symmetrically "
                    + "over all positions. Under those clauses, its two cross equalities are "
                    + "equivalent to clause (4). One-based odd position means val(i) mod 2 = 0; "
                    + "mod denotes natural-number remainder.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("config-thirty-eight", "Theorem 3.8 configuration", "Config38",
                Config38Formula(),
                "Theorem 3.8 states the following clauses verbatim: “(1) lambda(p_1) = "
                    + "lambda(p_{2n+1}) = lambda(q_1) = lambda(q_{2n+1}) for every n in "
                    + "{1, 2, ..., (m-1)/2}, (2) lambda(p_{2n}) = lambda(q_{2n}) for every n "
                    + "in {1, 2, ..., (m-1)/2}, (3) lambda({p_i, p_{i+1}}) = "
                    + "lambda({q_j, q_{j+1}}) and lambda({p_j, p_{j+1}}) = "
                    + "lambda({q_i, q_{i+1}}), for all odd i in {1, 2, ..., m} and all even "
                    + "j in {1, 2, ..., m}.” The printed range in clause (3) reaches m, but "
                    + "the edge {p_m,p_{m+1}} does not exist. Config38 therefore quantifies "
                    + "over the actual edge positions 1 through m-1. One-based parity is "
                    + "expressed by val(i) mod 2, with zero for odd positions and one for even "
                    + "positions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gobel-misra-claim", "Conjecture 5.3", "claim", ClaimFormula(),
                "Conjecture 5.3 reads verbatim: “Let P and Q be two colored paths on m vertices "
                    + "with det(K_P) = det(K_Q). (1) If m is even, then one of the following "
                    + "conditions holds: • Q is identical to P, • Q is a reflection of P, • P "
                    + "and Q satisfy the color configuration stated in Theorem 3.6 or is a "
                    + "reflection of the same. (2) Similarly, if m is odd, then one of the "
                    + "following conditions holds: • Q is identical to P, • Q is a reflection "
                    + "of P, • P and Q satisfy the color configuration stated in Theorem 3.8 "
                    + "or is a reflection of the same.” The displayed claim reads the final "
                    + "reflection phrase in its widest form: neither path, P alone, Q alone, or "
                    + "both paths may be reflected.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gobel-misra-refutation", "Conjecture 5.3 is false", "result",
                ResultFormula(),
                "Take one vertex color a, two edge colors u and v, and m=7. The edge sequences "
                    + "P=(u,v,v,u,u,v) and Q=(u,u,v,u,v,v) have the common determinant "
                    + "a^7-3a^5u^2-3a^5v^2+2a^3u^4+6a^3u^2v^2+2a^3v^4-2au^4v^2-2au^2v^4. "
                    + "They are neither identical nor reflections. The four Config38 variants "
                    + "all fail their edge clause: for (P,Q), e_1(P)=u differs from e_6(Q)=v; "
                    + "for (reflect(P),Q), e_1(reflect(P))=v differs from e_2(Q)=u; for "
                    + "(P,reflect(Q)), e_3(P)=v differs from e_6(reflect(Q))=u; and for the "
                    + "double reflection, e_1(reflect(P))=v differs from "
                    + "e_6(reflect(Q))=u.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "gobel-misra-colored-path-determinant-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula ColoredPathFormula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var fields = Seq(
            OpenBrace,
            F.Id("vertexColor"), Colon, Sp, Arrow(Fin(m), v), Semi, Sp,
            F.Id("edgeColor"), Colon, Sp, Arrow(Fin(Subtract(m, D(1))), e),
            CloseBrace);
        return Disp(Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
            Equal(Call("ColoredPath", v, e, m), fields)))));
    }

    private static Formula ConcentrationFormula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var p = F.Id("P");
        var i = F.Id("i");
        var j = F.Id("j");
        var value = Cases(
            CaseRow(Call("X", Call("inl", Call("vertexColor", p, i))), Equal(i, j)),
            CaseRow(Call("X", Call("inr", Call("edgeColor", p,
                    Call("Fin.mk", Call("val", i))))),
                Equal(Add(Call("val", i), D(1)), Call("val", j))),
            CaseRow(Call("X", Call("inr", Call("edgeColor", p,
                    Call("Fin.mk", Call("val", j))))),
                Equal(Add(Call("val", j), D(1)), Call("val", i))),
            CaseRow(D(0), Named("otherwise")));
        var path = Call("ColoredPath", v, e, m);
        var equation = Equal(Call("entry", Call("concentration", p), i, j), value);
        return Disp(Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
            Bound("P", path, Bound("i", Fin(m), Bound("j", Fin(m), equation)))))));
    }

    private static Formula ReflectFormula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var p = F.Id("P");
        var i = F.Id("i");
        var reflected = Call("reflect", p);
        var vertex = Bound("i", Fin(m), Equal(
            Call("vertexColor", reflected, i),
            Call("vertexColor", p,
                Call("Fin.mk", Subtract(Subtract(m, D(1)), Call("val", i))))));
        var edge = Bound("i", Fin(Subtract(m, D(1))), Equal(
            Call("edgeColor", reflected, i),
            Call("edgeColor", p,
                Call("Fin.mk", Subtract(Subtract(m, D(2)), Call("val", i))))));
        return Disp(Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
            Bound("P", Call("ColoredPath", v, e, m), And(vertex, edge))))));
    }

    private static Formula Config36Formula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var p = F.Id("P");
        var q = F.Id("Q");
        var i = F.Id("i");
        var j = F.Id("j");
        var vertices = Fin(m);
        var edges = Fin(Subtract(m, D(1)));
        var sameEdges = Bound("i", edges,
            Equal(Call("edgeColor", p, i), Call("edgeColor", q, i)));
        var oddVertices = Bound("i", vertices, Bound("j", vertices,
            Implies(And(OddPosition(i), OddPosition(j)), And(
                Equal(Call("vertexColor", p, i), Call("vertexColor", p, j)),
                Equal(Call("vertexColor", q, i), Call("vertexColor", q, j))))));
        var evenVertices = Bound("i", vertices, Bound("j", vertices,
            Implies(And(EvenPosition(i), EvenPosition(j)), And(
                Equal(Call("vertexColor", p, i), Call("vertexColor", p, j)),
                Equal(Call("vertexColor", q, i), Call("vertexColor", q, j))))));
        var crossed = Bound("i", vertices, Bound("j", vertices,
            Implies(And(OddPosition(i), EvenPosition(j)), And(
                Equal(Call("vertexColor", p, i), Call("vertexColor", q, j)),
                Equal(Call("vertexColor", p, j), Call("vertexColor", q, i))))));
        var body = Iff(Config("Config36", p, q),
            And(sameEdges, oddVertices, evenVertices, crossed));
        return Disp(Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
            Bound("P", Call("ColoredPath", v, e, m),
                Bound("Q", Call("ColoredPath", v, e, m), body))))));
    }

    private static Formula Config38Formula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var p = F.Id("P");
        var q = F.Id("Q");
        var i = F.Id("i");
        var j = F.Id("j");
        var vertices = Fin(m);
        var edges = Fin(Subtract(m, D(1)));
        var oddVertices = Bound("i", vertices, Bound("j", vertices,
            Implies(And(OddPosition(i), OddPosition(j)), And(
                Equal(Call("vertexColor", p, i), Call("vertexColor", p, j)),
                Equal(Call("vertexColor", p, i), Call("vertexColor", q, j)),
                Equal(Call("vertexColor", q, i), Call("vertexColor", q, j))))));
        var evenVertices = Bound("i", vertices, Implies(EvenPosition(i),
            Equal(Call("vertexColor", p, i), Call("vertexColor", q, i))));
        var forwardEdges = Bound("i", edges, Bound("j", edges,
            Implies(And(OddPosition(i), EvenPosition(j)),
                Equal(Call("edgeColor", p, i), Call("edgeColor", q, j)))));
        var reverseEdges = Bound("i", edges, Bound("j", edges,
            Implies(And(OddPosition(i), EvenPosition(j)),
                Equal(Call("edgeColor", p, j), Call("edgeColor", q, i)))));
        var body = Iff(Config("Config38", p, q),
            And(oddVertices, evenVertices, forwardEdges, reverseEdges));
        return Disp(Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
            Bound("P", Call("ColoredPath", v, e, m),
                Bound("Q", Call("ColoredPath", v, e, m), body))))));
    }

    private static Formula ClaimFormula()
    {
        var v = F.Id("V");
        var e = F.Id("E");
        var m = F.Id("m");
        var p = F.Id("P");
        var q = F.Id("Q");
        var path = Call("ColoredPath", v, e, m);
        var determinantEquality = Equal(
            Call("det", Call("concentration", p)),
            Call("det", Call("concentration", q)));
        var evenConfigurations = Or(
            Config("Config36", p, q),
            Config("Config36", Reflect(p), q),
            Config("Config36", p, Reflect(q)),
            Config("Config36", Reflect(p), Reflect(q)));
        var oddConfigurations = Or(
            Config("Config38", p, q),
            Config("Config38", Reflect(p), q),
            Config("Config38", p, Reflect(q)),
            Config("Config38", Reflect(p), Reflect(q)));
        var alternatives = Or(
            Equal(q, p),
            Equal(q, Reflect(p)),
            And(Call("Even", m), evenConfigurations),
            And(Call("Odd", m), oddConfigurations));
        var body = Implies(determinantEquality, alternatives);
        return Disp(Iff(F.Id("claim"),
            Bound("V", Types(), Bound("E", Types(), Bound("m", Naturals(),
                Bound("P", path, Bound("Q", path, body)))))));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Types() => Named("Type");
    private static Formula Naturals() => Named("Nat");
    private static Formula Named(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Reflect(Formula path) => Call("reflect", path);
    private static Formula Config(string name, Formula left, Formula right) =>
        Call(name, left, right);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Bound(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments)
    {
        if (!name.Contains('.'))
            return new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

        var parts = name.Split('.');
        Formula function = F.Id(parts[0]);
        for (var index = 1; index < parts.Length; index++)
            function = Seq(function, Dot, F.Id(parts[index]));
        return new Formula.Apply(function, [.. arguments]);
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula OddPosition(Formula index) =>
        Equal(Call("mod", Call("val", index), D(2)), D(0));
    private static Formula EvenPosition(Formula index) =>
        Equal(Call("mod", Call("val", index), D(2)), D(1));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.Or, result);
        return result;
    }

    private static Formula CaseRow(Formula value, Formula condition) =>
        Seq(value, Sp, Amp, Sp, condition);

    private static Formula Cases(params Formula[] rows)
    {
        var items = new System.Collections.Generic.List<Formula>
        {
            Begin, Grp(F.Id("cases")),
        };
        for (var index = 0; index < rows.Length; index++)
        {
            if (index > 0)
                items.Add(RowBreak);
            items.Add(rows[index]);
        }
        items.Add(End);
        items.Add(Grp(F.Id("cases")));
        return Seq([.. items]);
    }
}
