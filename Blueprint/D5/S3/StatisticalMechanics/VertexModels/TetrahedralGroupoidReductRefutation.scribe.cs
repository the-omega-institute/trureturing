using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class TetrahedralGroupoidReductRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/bardakov2024simplex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first tetrahedral groupoid can have a reduct that is not a reduced first tetrahedral groupoid. On Bool, take circ to be conjunction and star, lt and rt to be left projections. This answers the question in Section 9.2 of Bardakov et al., arXiv:2206.08906v1.",
        H("A T1-groupoid whose reduct is not reduced"),
        Blocks(
            Node("tgroupoid", "The four-operation axioms", T1Formula(),
                "For a type X and four binary operations star, circ, lt and rt on X, IsT1Groupoid is the conjunction of these four identities, in the printed order. The operations star, circ, lt and rt denote the paper's star, circle, left triangle and right triangle operations.",
                "IsT1Groupoid"),
            Node("reduced", "The two-operation axioms", ReducedFormula(),
                "For a type X and binary operations star and circ on X, IsReducedT1Groupoid is the conjunction of these three identities, in the printed order. Its first identity constrains circ itself, whereas the first four-operation identity uses lt in both arguments of circ.",
                "IsReducedT1Groupoid"),
            Node("claim", "The universal reduct assertion", ClaimFormula(),
                "The assertion says that for every type X and all four binary operations on X, the four T1 identities imply the three reduced identities after forgetting lt and rt.",
                "claim"),
            Node("result", "The assertion is false", Disp(Seq(Neg, Sp, Named(F.Id("claim")))),
                "Set X = Bool, circ(x, y) = x && y, and star(x, y) = lt(x, y) = rt(x, y) = x. The two sides of each of the first two T1 identities equal x && y, and the two sides of each of the last two equal x. The first reduced identity at x = y = true and z = false would equate true with false. Thus these operations form a T1-groupoid whose reduct is not reduced.",
                "result", AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bardakov-2022-t1-groupoid-reduct-question"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration,
        AssessedProvenance? provenance = null, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("tetrahedral-reduct-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula operation, params Formula[] arguments) =>
        new Formula.Apply(operation, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula AndAlso(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula T1(params Formula[] operations) =>
        Call(Seq(F.Id("IsT"), D(1), F.Id("Groupoid")), operations);
    private static Formula Reduced(params Formula[] operations) =>
        Call(Seq(F.Id("IsReducedT"), D(1), F.Id("Groupoid")), operations);

    private static Formula Operations(Formula body, bool triangles)
    {
        Formula x = F.Id("X");
        Formula binary = Seq(x, Sp, To, Sp, Parenthesized(Seq(x, Sp, To, Sp, x)));
        if (triangles)
            body = All("lt", binary, All("rt", binary, body));
        return All("X", Named(F.Id("Type")), All("star", binary, All("circ", binary, body)));
    }

    private static Formula ThreeVariables(Formula body) =>
        All("x", F.Id("X"), All("y", F.Id("X"), All("z", F.Id("X"), body)));

    private static Formula CompatibilityFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), w = F.Id("w");
        Formula star = F.Id("star"), circ = F.Id("circ");
        return ThreeVariables(All("w", F.Id("X"),
            Equal(At(star, At(circ, x, y), At(circ, z, w)),
                At(circ, At(star, x, z), At(star, y, w)))));
    }

    private static Formula T1Formula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula star = F.Id("star"), circ = F.Id("circ"), lt = F.Id("lt"), rt = F.Id("rt");
        Formula first = ThreeVariables(Equal(At(circ, x, y), At(circ, At(lt, x, z), At(lt, y, z))));
        Formula third = ThreeVariables(Equal(At(rt, At(rt, x, y), z),
            At(rt, At(rt, x, z), At(star, y, z))));
        Formula fourth = ThreeVariables(Equal(At(lt, At(star, x, y), z), At(rt, x, At(circ, y, z))));
        return Disp(Operations(IffTo(T1(star, circ, lt, rt),
            AndAlso(first, AndAlso(CompatibilityFormula(), AndAlso(third, fourth)))), true));
    }

    private static Formula ReducedFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula star = F.Id("star"), circ = F.Id("circ");
        Formula first = ThreeVariables(Equal(At(circ, x, y),
            At(circ, At(circ, x, z), At(circ, y, z))));
        Formula second = ThreeVariables(Equal(At(star, At(star, x, y), z),
            At(star, At(star, x, z), At(star, y, z))));
        return Disp(Operations(IffTo(Reduced(star, circ),
            AndAlso(first, AndAlso(second, CompatibilityFormula()))), false));
    }

    private static Formula ClaimFormula()
    {
        Formula star = F.Id("star"), circ = F.Id("circ"), lt = F.Id("lt"), rt = F.Id("rt");
        Formula implication = new Formula.Logic(T1(star, circ, lt, rt),
            FormulaLogicOperator.Implies, Reduced(star, circ));
        return Disp(IffTo(Named(F.Id("claim")), Operations(implication, true)));
    }
}
