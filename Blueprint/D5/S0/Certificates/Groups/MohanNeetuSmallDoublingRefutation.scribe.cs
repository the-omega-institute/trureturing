using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Groups;

internal sealed class MohanNeetuSmallDoublingRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mohan2026smalldoubling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two explicit three-element subsets of the Klein bottle group contradict all three "
            + "small-doubling conjectures printed in section 6.",
        H("Small Doubling in the Klein Bottle Group"),
        Blocks(
            LiteratureDefinition(
                "mohan-neetu-klein-bottle-group",
                "The coordinate group",
                "KleinBottleGroup",
                KleinBottleGroupFormula(),
                "The carrier consists of integer pairs. It is the paper's Z semidirect Z "
                    + "at q = -1, the Klein bottle group BS(1,-1)."),
            LiteratureDefinition(
                "mohan-neetu-klein-bottle-group-instance",
                "The printed coordinate law",
                "instGroupKleinBottleGroup",
                GroupInstanceFormula(),
                "Multiplication is (r,n)(s,m) = (r + (-1)^n s,n+m), the identity is "
                    + "(0,0), and the inverse of (r,n) is (-(-1)^n r,-n)."),
            LiteratureDefinition(
                "mohan-neetu-torsion-free-group",
                "Torsion freeness",
                "IsTorsionFreeGroup",
                TorsionFreeFormula(),
                "A group is torsion-free when every nonidentity element has infinite order. "
                    + "Equivalently, no nonidentity element satisfies IsOfFinOrder."),
            LiteratureDefinition(
                "mohan-neetu-abelian-set",
                "Abelian subsets",
                "IsAbelianSet",
                AbelianSetFormula(),
                "The paper states: \"A set S is said to be abelian if ⟨S⟩ is an abelian "
                    + "subgroup of G.\" Subgroup.closure is the generated subgroup."),
            LiteratureDefinition(
                "mohan-neetu-conjecture-63",
                "Conjecture 6.3",
                "claim63",
                Claim63Formula(),
                "The paper states: \"Conjecture 6.3. Let S be a nonempty finite subset of a "
                    + "torsion-free group G with |S| ≥ 3 and e ∈ S. If |S²| ≤ 3|S| − 3, "
                    + "then ⟨S⟩ is an abelian subgroup of G.\" Finsets supply finiteness; "
                    + "the cardinality premise also supplies nonemptiness. DecidableEq is "
                    + "implementation structure, classically available for every type."),
            LiteratureDefinition(
                "mohan-neetu-conjecture-61",
                "Conjecture 6.1",
                "claim61",
                Claim61Formula(),
                "The paper states: \"Conjecture 6.1. Let S be a nonempty finite subset of a "
                    + "torsion-free group G such that S = A ∪ B, where A and B are disjoint "
                    + "abelian sets. If |S²| ≤ 3k − 3, ⟨S⟩ is abelian.\" Here k = |S|. "
                    + "DecidableEq is implementation structure, classically available for "
                    + "every type."),
            LiteratureDefinition(
                "mohan-neetu-conjecture-62",
                "Conjecture 6.2",
                "claim62",
                Claim62Formula(),
                "The paper states: \"Conjecture 6.2. Let S be a nonempty finite subset of a "
                    + "torsion-free group G such that S = A ∪ B ∪ C, where A, B, C are "
                    + "pairwise disjoint abelian sets. If |S²| ≤ 3k − 4, ⟨S⟩ is abelian.\" "
                    + "Here k = |S|. DecidableEq is implementation structure, classically "
                    + "available for every type."),
            RepositoryTheorem(
                "mohan-neetu-conjecture-63-counterexample",
                "A counterexample containing the identity",
                "result63",
                ResultFormula("claim63"),
                "Take S = {(0,0),(0,1),(1,1)}. Its product set is "
                    + "{(-1,2),(0,0),(0,1),(0,2),(1,1),(1,2)}, so |S|=3 and "
                    + "|S²|=6=3|S|-3. The identity belongs to S, while "
                    + "(0,1)(1,1)=(-1,2) and (1,1)(0,1)=(1,2). The coordinate proof "
                    + "that the ambient group is torsion-free is shared by all three results."),
            RepositoryTheorem(
                "mohan-neetu-conjecture-61-counterexample",
                "Two disjoint abelian pieces",
                "result61",
                ResultFormula("claim61"),
                "Use the same S, with A={(0,0),(0,1)} and B={(1,1)}. The pieces are "
                    + "disjoint and generate abelian subgroups, while S has the same six "
                    + "products and contains the same noncommuting pair."),
            RepositoryTheorem(
                "mohan-neetu-conjecture-62-counterexample",
                "Three singleton abelian pieces",
                "result62",
                ResultFormula("claim62"),
                "Take S={(1,1),(2,1),(3,1)} and let A, B and C be its singleton "
                    + "pieces. The product set is {(-2,2),(-1,2),(0,2),(1,2),(2,2)}, "
                    + "so |S²|=5=3|S|-4. Yet (1,1)(2,1)=(-1,2) and "
                    + "(2,1)(1,1)=(1,2)."))));

    private static DocumentBlock LiteratureDefinition(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock RepositoryTheorem(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula KleinBottleGroupFormula() => Disp(Equal(
        F.Id("KleinBottleGroup"),
        Seq(OpenBrace, F.Id("r"), Colon, Sp, Integers(), Comma, Sp,
            F.Id("n"), Colon, Sp, Integers(), CloseBrace)));

    private static Formula GroupInstanceFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var multiplication = All("a", KleinBottleGroup(), All("b", KleinBottleGroup(),
            Equal(Multiply(a, b), Pair(
                Add(Field(a, "r"), Multiply(NegOnePow(Field(a, "n")), Field(b, "r"))),
                Add(Field(a, "n"), Field(b, "n"))))));
        var identity = Equal(D(1), Pair(D(0), D(0)));
        var inverse = All("a", KleinBottleGroup(), Equal(
            Inverse(a), Pair(
                new Formula.Negate(Multiply(NegOnePow(Field(a, "n")), Field(a, "r"))),
                new Formula.Negate(Field(a, "n")))));
        return Disp(And(multiplication, And(identity, inverse)));
    }

    private static Formula TorsionFreeFormula()
    {
        var g = F.Id("g");
        var group = F.Id("G");
        var definition = Iff(
            Call("IsTorsionFreeGroup", group),
            All("g", group, Implies(NotEqual(g, D(1)),
                new Formula.Not(Call("IsOfFinOrder", g)))));
        return Disp(All("G", F.Id("Type"), Implies(Call("Group", group), definition)));
    }

    private static Formula AbelianSetFormula()
    {
        var group = F.Id("G");
        var x = F.Id("X");
        var a = F.Id("a");
        var b = F.Id("b");
        var commutes = All("a", group, Implies(Member(a, Closure(x)),
            All("b", group, Implies(Member(b, Closure(x)),
                Equal(Multiply(a, b), Multiply(b, a))))));
        var definition = All("X", Call("Set", group),
            Iff(Call("IsAbelianSet", x), commutes));
        return Disp(All("G", F.Id("Type"), Implies(Call("Group", group), definition)));
    }

    private static Formula Claim63Formula()
    {
        var group = F.Id("G");
        var s = F.Id("S");
        var setType = Call("Set", group);
        var body = Implies(Call("IsTorsionFreeGroup", group),
            All("S", Call("Finset", group),
                Implies(GreaterEqual(Card(s), D(3)),
                    Implies(Member(D(1), s),
                        Implies(LessEqual(Card(Multiply(s, s)),
                                Subtract(Multiply(D(3), Card(s)), D(3))),
                            Call("IsAbelianSet", Coerce(s, setType)))))));
        return Disp(Iff(F.Id("claim63"), GroupContext(group, body)));
    }

    private static Formula Claim61Formula()
    {
        var group = F.Id("G");
        var s = F.Id("S");
        var a = F.Id("A");
        var b = F.Id("B");
        var finset = Call("Finset", group);
        var setType = Call("Set", group);
        var body = Implies(Call("IsTorsionFreeGroup", group),
            AllMany(
                [("S", finset), ("A", finset), ("B", finset)],
                Implies(Call("Nonempty", s),
                    Implies(Equal(s, Union(a, b)),
                        Implies(Call("Disjoint", a, b),
                            Implies(Call("IsAbelianSet", Coerce(a, setType)),
                                Implies(Call("IsAbelianSet", Coerce(b, setType)),
                                    Implies(LessEqual(Card(Multiply(s, s)),
                                            Subtract(Multiply(D(3), Card(s)), D(3))),
                                        Call("IsAbelianSet", Coerce(s, setType))))))))));
        return Disp(Iff(F.Id("claim61"), GroupContext(group, body)));
    }

    private static Formula Claim62Formula()
    {
        var group = F.Id("G");
        var s = F.Id("S");
        var a = F.Id("A");
        var b = F.Id("B");
        var c = F.Id("C");
        var finset = Call("Finset", group);
        var setType = Call("Set", group);
        var body = Implies(Call("IsTorsionFreeGroup", group),
            AllMany(
                [("S", finset), ("A", finset), ("B", finset), ("C", finset)],
                Implies(Call("Nonempty", s),
                    Implies(Equal(s, Union(Parenthesized(Union(a, b)), c)),
                        Implies(Call("Disjoint", a, b),
                            Implies(Call("Disjoint", a, c),
                                Implies(Call("Disjoint", b, c),
                                    Implies(Call("IsAbelianSet", Coerce(a, setType)),
                                        Implies(Call("IsAbelianSet", Coerce(b, setType)),
                                            Implies(Call("IsAbelianSet", Coerce(c, setType)),
                                                Implies(LessEqual(Card(Multiply(s, s)),
                                                        Subtract(Multiply(D(3), Card(s)), D(4))),
                                                    Call("IsAbelianSet", Coerce(s, setType)))))))))))));
        return Disp(Iff(F.Id("claim62"), GroupContext(group, body)));
    }

    private static Formula GroupContext(Formula group, Formula body) =>
        All("G", F.Id("Type"),
            Implies(Call("Group", group),
                Implies(Call("DecidableEq", group), body)));

    private static Formula ResultFormula(string claim) =>
        Disp(new Formula.Not(F.Id(claim)));

    private static Formula KleinBottleGroup() => F.Id("KleinBottleGroup");
    private static Formula Integers() => new Formula.Integers();
    private static Formula Closure(Formula set) => QualifiedCall("Subgroup", "closure", set);
    private static Formula Card(Formula set) => QualifiedCall("Finset", "card", set);
    private static Formula Field(Formula value, string field) =>
        Seq(Parenthesized(value), Dot, F.Id(field));
    private static Formula Pair(Formula first, Formula second) =>
        Parenthesized(Seq(first, Comma, Sp, second));
    private static Formula Union(Formula left, Formula right) =>
        Seq(left, Sp, Cup, Sp, right);
    private static Formula NegOnePow(Formula exponent) =>
        new Formula.Power(new Formula.Negate(D(1)), exponent);
    private static Formula Inverse(Formula value) =>
        new Formula.Power(value, new Formula.Negate(D(1)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(owner), Dot, F.Id(name)), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula AllMany((string Name, Formula Domain)[] variables, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))],
            body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula GreaterEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));
}
