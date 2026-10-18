using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class CayleyCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var cay = C("addCayley", I("S")); var sq = C("boxProd", cay, cay);
        var complete = Eq(cay, C("completeGraph", I("A")));
        var wc = C("WellCovered", sq);
        var allPowers = All("d", C("Nat"), Imp(Le(D(1), I("d")), C("WellCovered", C("power", sq, I("d")))));
        var formula = Groups(Imp(C("Connected", cay),
            And(Iff(complete, wc), Iff(wc, allPowers))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A connected finite abelian Cayley graph has a well-covered Cartesian square exactly when it is complete, and exactly when every positive distance power of that square is well-covered.",
            H("Characterizing well-covered Cayley squares"), Blocks(
                Node("CayleyCharacterization", "characterization", "All finite abelian groups and all positive powers", "cayley_square_characterization", formula,
                    "The group is arbitrary finite additive abelian; its connection set avoids zero and is closed under negation. Well-covered means that every pair of inclusion-maximal independent vertex sets has equal cardinality. If the graph is not complete, its independence number is at least two. The nearly-empty-layer construction produces a maximal square-independent set of size at most (n-1) alpha+1, strictly below the maximum n alpha supplied by the Cayley difference construction. For a complete graph, independent square-sets are matchings between rows and columns. Maximality saturates all rows and columns, giving cardinality n. The square has diameter at most two, so every power from two onward is complete. The first-power identity supplies the reverse implication. The trivial group and complete graphs of every positive order are included. The natural-distance power is used only after establishing actual connectedness of the square, so it agrees with the reachability-based distance-power definition."))));
    }
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Groups(Formula b)
    {
        var a = I("A"); var s = I("S"); var z = I("z");
        var inverse = All("z", a, Imp(C("Mem", z, s), C("Mem", C("neg", z), s)));
        var allowed = And(Not(C("Mem", D(0), s)), inverse);
        return All("A", C("Type"), Inst("Finite", a, Inst("AddCommGroup", a,
            All("S", C("Set", a), Imp(allowed, b)))));
    }
    private static DocumentBlock Node(string module, string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Products/" + module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/GraphInvariants/phamvu2026wellcoveredpowers"),
                LibraryNoteRef.Create("D5/L/GraphInvariants/hartnellrallwash2017cartesian")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
