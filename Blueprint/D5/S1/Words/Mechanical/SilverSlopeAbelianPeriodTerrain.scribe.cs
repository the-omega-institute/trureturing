using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class SilverSlopeAbelianPeriodTerrainDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/peltomaki2020abelianperiods");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pell approximation estimates and convergent-period constructions for the silver slope.",
        H("Silver Pell arithmetic and convergent periods"),
        Blocks(
            Node("convergent-realisation", "silver_q_realisation", "Every convergent denominator is a minimum period", Realisation(),
                "Proposition 5.5 is realised by a long list of equal-count blocks; every smaller period contradicts the endpoint error estimate.", true)), []));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodTerrain." + declaration),
            H(title), StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose + " The operators real and integer denote canonical numeric coercions."))), DescribeRole.Theorem);
    private static Formula K => F.Id("k");
    private static Formula A => Call("silverSlope");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q(Formula k) => Call("P", new Formula.Binary(k, FormulaBinaryOperator.Add, D(1)));
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Realisation() => Disp(All("k", N, Ex("n", N, Ex("i", N,
        And(Lt(D(0), F.Id("n")), Eq(Call("minAbelianPeriod", Call("lowerMechanicalFactor", A, D(0), F.Id("n"), F.Id("i"))), Q(K)))))));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);}
