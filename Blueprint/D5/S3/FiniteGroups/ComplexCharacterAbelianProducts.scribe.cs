using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class ComplexCharacterAbelianProductsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026finitecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restriction past an abelian direct factor preserves irreducibility over an algebraically closed field.",
        H("Irreducible representations of products with abelian groups"),
        Blocks(
            Node("central-scalar", "central_action_scalar", "Central elements act by scalars", CentralScalar(),
                "Schur's lemma identifies an intertwining endomorphism with scalar multiplication. A central group element gives such an endomorphism.", AssessedProvenance.FromLiterature(Source)),
            Node("product-degrees", "degreesProdAbelian", "The same simple degrees", ProductDegrees(),
                "The abelian second factor acts by scalars. Every subspace invariant under the first factor is therefore invariant under the whole product.", AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/FiniteGroups/ComplexCharacterAbelianProducts." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula CentralScalar()
    {
        Formula k = F.Id("k"), v = F.Id("V"), g = F.Id("G"), rho = F.Id("rho"), z = F.Id("z");
        Formula central = All("g", g, Equal(Mul(z, F.Id("g")), Mul(F.Id("g"), z)));
        Formula conclusion = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("c"), k,
            Equal(App(rho, z), App(Q("HSMul", "hSMul"), F.Id("c"),
                Parenthesized(Seq(Q("LinearMap", "id"), Colon, Sp, App(F.Id("LinearMap"), k, v, v))))));
        return FieldModule(k, v, All("G", Type(), WithInstance("Monoid", g,
            All("rho", App(F.Id("Representation"), k, g, v),
                WithInstance(Q("Representation", "IsIrreducible"), rho,
                    All("z", g, Imp(central, conclusion)))))));
    }

    private static Formula ProductDegrees()
    {
        Formula b = F.Id("B"), a = F.Id("A");
        Formula Degrees(Formula group)
        {
            Formula d = F.Id("d"), x = F.Id("X");
            Formula member = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("X"),
                App(F.Id("FDRep"), Seq(Mathbb, Grp(F.Id("C"))), group),
                new Formula.Logic(App(Q("CategoryTheory", "Simple"), x), FormulaLogicOperator.And,
                    Equal(App(Q("Module", "finrank"), Seq(Mathbb, Grp(F.Id("C"))), x), d)));
            return Seq(OpenBrace, d, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Bar, Sp, member, CloseBrace);
        }
        return All("B", F.Id("Type"), WithInstance("Group", b,
            All("A", F.Id("Type"), WithInstance("CommGroup", a,
                Equal(Degrees(Parenthesized(Seq(b, Sp, Times, Sp, a))), Degrees(b))))));
    }

    private static Formula FieldModule(Formula k, Formula v, Formula body) =>
        All("k", Type(), WithInstance("Field", k, WithInstance("IsAlgClosed", k,
            All("V", Type(), WithInstance("AddCommGroup", v,
                WithInstance(App(F.Id("Module"), k), v,
                    WithInstance(App(F.Id("FiniteDimensional"), k), v, body)))))));
    private static Formula WithInstance(string name, Formula arg, Formula body) => WithInstance(F.Id(name), arg, body);
    private static Formula WithInstance(Formula name, Formula arg, Formula body) =>
        Seq(OpenBracket, App(name, arg), CloseBracket, Comma, Sp, body);
    private static Formula Type() => Seq(F.Id("Type"), Star);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
