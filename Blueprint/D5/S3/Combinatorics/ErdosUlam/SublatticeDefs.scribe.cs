using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ErdosUlam;

internal sealed class SublatticeDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean sublattices are represented by subsets or by bitmasks.", H("Boolean sublattices and prefix chains"),
        Blocks(
            Node("sublattice", "Nonempty sublattices", "IsSublattice", SublatticeFormula(),
                "A sublattice is a nonempty finite family closed under union and intersection.", DescribeRole.Definition),
            Node("monochromatic", "Constant colour", "Monochromatic", MonochromaticFormula(),
                "All members of a monochromatic family have one common Boolean colour.", DescribeRole.Definition),
            Node("prefix-card", "Cardinality of a prefix", "prefix_card", PrefixFormula(),
                "The prefix of rank r consists of the first r elements when r is at most n. Prefixes are nested by rank. Bitmask decoding sends bitwise union and intersection to the corresponding subset operations.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bool() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula Sets(Formula n) => Call("Finset", Call("Fin", n));
    private static Formula Families(Formula n) => Call("Finset", Sets(n));
    private static Formula Colourings(Formula n) => new Formula.TypeArrow(Sets(n), Bool());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    private static Formula SublatticeFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var a = F.Id("A"); var b = F.Id("B");
        var closure = All("A", Sets(n), Imp(Mem(a, l), All("B", Sets(n), Imp(Mem(b, l),
            And(Mem(Call("union", a, b), l), Mem(Call("inter", a, b), l))))));
        return Disp(All("n", Nat(), All("L", Families(n),
            Iff(Call("IsSublattice", l), And(Call("Nonempty", l), closure)))));
    }

    private static Formula MonochromaticFormula()
    {
        var n = F.Id("n"); var chi = F.Id("chi"); var l = F.Id("L");
        var a = F.Id("A"); var b = F.Id("b");
        var constant = Ex("b", Bool(), All("A", Sets(n), Imp(Mem(a, l), Eqn(Call("chi", a), b))));
        return Disp(All("n", Nat(), All("chi", Colourings(n), All("L", Families(n),
            Iff(Call("Monochromatic", chi, l), constant)))));
    }



    private static Formula PrefixFormula()
    {
        var n = F.Id("n"); var r = F.Id("r");
        return Disp(All("n", Nat(), All("r", Nat(), Imp(Leq(r, n),
            Eqn(Call("card", Call("initialSegment", n, r)), r)))));
    }
}
