using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrobeniusCharacterDegreesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026finitecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-point-free conjugation on an abelian normal subgroup constrains simple complex degrees.",
        H("Degrees over an abelian normal subgroup"),
        Blocks(Node("degree_square_le_card", "The degree-square bound", Square(),
            "The group algebra maps onto the endomorphism algebra of a simple representation. Comparing dimensions bounds the square of its degree by the group order."),
            Node("degree_dvd_or_index_dvd_of_fixedPointFree", "The divisibility dichotomy", Dichotomy(),
            "A nontrivial simple constituent of the restriction has inertia subgroup equal to the normal subgroup. Clifford decomposition then makes the subgroup index divide the degree. A trivial constituent makes the representation descend to the quotient, where its degree divides the quotient order."))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("frobenius-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/FrobeniusCharacterDegrees." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Square()
    {
        Formula g = F.Id("G"), x = F.Id("X");
        return Group("G", All("X", App(F.Id("FDRep"), Complex(), g),
            Instance(App(Q("CategoryTheory", "Simple"), x),
                new Formula.Relation(new Formula.Power(Degree(x), D(2)), FormulaRelationOperator.LessThanOrEqual,
                    App(Q("Nat", "card"), g)))));
    }
    private static Formula Dichotomy()
    {
        Formula k = F.Id("K"), n = F.Id("N"), g = F.Id("g"), v = F.Id("n"), w = F.Id("W");
        Formula fixedFree = All("g", k, Imp(new Formula.Not(Member(g, n)),
            All("n", n, Imp(Equal(App(Q("MulAut", "conjNormal"), g, v), v), Equal(v, D(1))))));
        Formula index = App(Q("Subgroup", "index"), n);
        Formula conclusion = new Formula.Logic(Parenthesized(Divides(Degree(w), index)), FormulaLogicOperator.Or,
            Parenthesized(Divides(index, Degree(w))));
        return Group("K", All("N", App(F.Id("Subgroup"), k),
            Instance(App(Q("Subgroup", "Normal"), n), Instance(App(F.Id("IsMulCommutative"), n),
                Imp(fixedFree, All("W", App(F.Id("FDRep"), Complex(), k),
                    Instance(App(Q("CategoryTheory", "Simple"), w), conclusion)))))));
    }
    private static Formula Group(string name, Formula body) => All(name, F.Id("Type"),
        Instance(App(F.Id("Group"), F.Id(name)), Instance(App(F.Id("Finite"), F.Id(name)), body)));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Degree(Formula v) => App(Q("Module", "finrank"), Complex(), v);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
}
