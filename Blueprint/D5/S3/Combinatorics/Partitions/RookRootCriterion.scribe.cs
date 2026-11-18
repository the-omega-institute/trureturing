using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookRootCriterion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source root filter is equivalent to geometric uniqueness of a partial column in each level.",
        H("Geometric singleton columns and the root floor condition"),
        Blocks(
            Definition("SingletonColumns", "The geometric singleton condition",
                "For each pair of column positions i and j, if both heights have nonzero remainder modulo m and their natural quotients by m agree, then i=j. A nonzero remainder means the column ends strictly inside that level; full and zero columns are excluded from partial tops. Thus every level has at most one partially filled column. This criterion concerns actual column heights, not an ordering of root labels."),
            Definition("root", "Integer roots",
                "At zero-based position i the root is mi minus the column height. Arithmetic takes place in the integers, so negative roots are retained."),
            Definition("RootFloorCriterion", "The original conditional floor test",
                "At adjacent positions i,j with j=i+1, impose root(j)/m at most root(i)/m only if neither root is divisible by m. Integer Euclidean division is floor division for positive m. Multiplying those quotients by positive m gives the source m-floor version with the same inequality direction."),
            Describe.Lean(DescribeId.Create("rookrootcriterion-geometric-iff"),
                DeclarationHandle.Create(Prefix + "rootFloorCriterion_iff_singleton"),
                H("Exact criterion for every padded Ferrers tuple"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every positive m and every weakly increasing nonnegative padded tuple d, the root floor test is equivalent to SingletonColumns. For a partial column, floor((mi-d(i))/m)=i-floor(d(i)/m)-1. The adjacent root inequality therefore forces a strict increase in the partial-top level. If two separated partial columns had the same level, monotonicity would put their intervening successor in that same level and contradict the adjacent condition. Conversely, geometric uniqueness forces every adjacent pair of partial tops into different levels. Zero padding and an empty index type need no exceptions. This formalizes the geometric content of the root criterion; equality of native rook numbers and root multisets is a separate unproved interface."))), DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rookrootcriterion-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Statement()
    {
        Formula m = F.Id("m"), n = F.Id("n"), d = F.Id("d"), nat = F.Id("Nat");
        return All("m", nat, Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m),
            All("n", nat, All("d", new Formula.TypeArrow(Call("Fin", n), nat),
                Imp(Call("Monotone", d), new Formula.Logic(
                    Call("RootFloorCriterion", m, Call("root", m, d)), FormulaLogicOperator.Iff,
                    Call("SingletonColumns", m, d)))))));
    }
}
