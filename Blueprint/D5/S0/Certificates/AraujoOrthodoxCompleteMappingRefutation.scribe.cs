using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class AraujoOrthodoxCompleteMappingRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/araujo2026completemappings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-element orthodox semigroup with an idempotent full-ordering product has no complete mapping.",
        H("Problem 15.5 on Complete Mappings of Orthodox Semigroups"),
        Blocks(
            Node(
                "araujo-orthodox-semigroup",
                "Orthodox semigroups",
                "Orthodox",
                OrthodoxFormula(),
                "In every display the antecedent Semigroup(S) renders Lean's typeclass binder "
                    + "[Semigroup S]. Regularity requires, for every x, an element y with "
                    + "x*y*x = x. "
                    + "The second conjunct says that the product of any two idempotents is "
                    + "idempotent, exactly the E-semigroup condition. Their conjunction is the "
                    + "paper's definition of orthodox.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "araujo-complete-mapping",
                "Complete mappings",
                "CompleteMapping",
                CompleteMappingFormula(),
                "The word Bijective in the display denotes Lean's Function.Bijective. Thus alpha "
                    + "and the product map x |-> x*alpha(x) must both be bijections, matching the "
                    + "definition in the abstract.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "araujo-idempotent-ordering",
                "An ordering with idempotent product",
                "IdempotentOrdering",
                IdempotentOrderingFormula(),
                "Here cons(c,l) is Lean's list c :: l, Nodup excludes repeated elements, and "
                    + "the universal membership clause makes the list exhaustive. The expression "
                    + "foldl(mul,c,l) is l.foldl (dot * dot) c, so p is the left-associated "
                    + "product of the ordering. The final clause is p*p = p.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "araujo-problem-fifteen-five",
                "Problem 15.5 as a universal claim",
                "claim",
                ClaimFormula(),
                "The question is read universally over every type carrying a semigroup structure. "
                    + "An orthodox semigroup with an idempotent ordering product is asserted to "
                    + "admit a complete mapping.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "araujo-problem-fifteen-five-refuted",
                "Problem 15.5 has a negative answer",
                "result",
                ResultFormula(),
                "The counterexample has elements w0, w1, w2, w3, w4 and multiplication rows "
                    + "[w0,w1,w2,w3,w4], [w1,w0,w2,w3,w4], [w2,w2,w2,w3,w4], "
                    + "[w3,w3,w3,w4,w2], and [w4,w4,w4,w2,w3]. It is associative and regular; "
                    + "its idempotents are w0 and w2 and are closed under multiplication. The "
                    + "ordering [w0,w1,w2,w3,w4] has product w2. Exhaustive kernel reduction "
                    + "checks all 3125 maps from the carrier to itself and finds no complete "
                    + "mapping. The semigroup has no absorbing zero.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "araujo-2026-orthodox-idempotent-ordering-complete-mapping-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula OrthodoxFormula()
    {
        var s = F.Id("S");
        var x = F.Id("x");
        var y = F.Id("y");
        var e = F.Id("e");
        var f = F.Id("f");
        var regular = All("x", s,
            ExistsOne("y", s, Equal(Multiply(Multiply(x, y), x), x)));
        var closed = All(["e", "f"], s,
            Implies(Equal(Multiply(e, e), e),
                Implies(Equal(Multiply(f, f), f),
                    Equal(
                        Multiply(
                            Parenthesized(Multiply(e, f)),
                            Parenthesized(Multiply(e, f))),
                        Multiply(e, f)))));
        return Disp(All("S", Types(),
            Implies(Call("Semigroup", s),
                Iff(Call("Orthodox", s), And(regular, closed)))));
    }

    private static Formula CompleteMappingFormula()
    {
        var s = F.Id("S");
        var alpha = F.Id("alpha");
        var x = F.Id("x");
        var productMap = Lambda("x", Multiply(x, Call("alpha", x)));
        var definition = Iff(
            Call("CompleteMapping", alpha),
            And(Call("Bijective", alpha), Call("Bijective", productMap)));
        return Disp(All("S", Types(),
            Implies(Call("Semigroup", s), All("alpha", Map(s, s), definition))));
    }

    private static Formula IdempotentOrderingFormula()
    {
        var s = F.Id("S");
        var c = F.Id("c");
        var l = F.Id("l");
        var x = F.Id("x");
        var ordering = Call("cons", c, l);
        var p = Call("foldl", F.Id("mul"), c, l);
        var exhaustive = All("x", s, Member(x, ordering));
        var clauses = And(Call("Nodup", ordering),
            And(exhaustive, Equal(Multiply(p, p), p)));
        var existsOrdering = ExistsMany(
            [("c", s), ("l", Call("List", s))], clauses);
        return Disp(All("S", Types(),
            Implies(Call("Semigroup", s),
                Iff(Call("IdempotentOrdering", s), existsOrdering))));
    }

    private static Formula ClaimFormula()
    {
        var s = F.Id("S");
        var alpha = F.Id("alpha");
        var conclusion = ExistsOne("alpha", Map(s, s), Call("CompleteMapping", alpha));
        var body = Implies(Call("Semigroup", s),
            Implies(Call("Orthodox", s),
                Implies(Call("IdempotentOrdering", s), conclusion)));
        return Disp(Iff(F.Id("claim"), All("S", Types(), body)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula All(string[] names, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), domain))],
            body);

    private static Formula ExistsOne(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula ExistsMany(
        (string Name, Formula Domain)[] variables,
        Formula body) => new Formula.BindMany(
            FormulaQuantifier.Exists,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))],
            body);

    private static Formula Lambda(string name, Formula body) =>
        Seq(F.LambdaLower, Sp, F.Id(name), Comma, Sp, body);

    private static Formula Map(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Types() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
}
