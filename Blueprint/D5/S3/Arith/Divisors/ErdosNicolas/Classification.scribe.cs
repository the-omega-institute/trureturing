using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/Classification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong induction from six checked finite certificate obligations", H("Strong induction from six checked finite certificate obligations"), Blocks(
            Node("good_of_finite_certificates", "The complete strengthened induction", InductionFormula(),
                "Good(n) states τ(n)<Ĥ(n) and 7Ĥ(n)<8τ(n) for n in E={12,24,60,120,180,240,360,420,720,840,1260,1680,2520,5040}; outside E it states Ĥ(n)<τ(n). The six finite obligations are the base interval, exceptional small lifts, exceptional large lifts, residue-tree leaves, the main exponent box, and six extras. Strong induction uses only the positive smaller inputs n/p and n/pᵃ. Two exponent cutoffs, largest-prime cutoffs 677 and 107, and modular chains reduce every remaining branch to one of the six obligations. ResidueTreeOK is conditional on the bound for the smaller input; it does not assume the desired current conclusion."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false, bool literature = false) => Describe.Lean(
        DescribeId.Create("erdosnicolas-classification-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula InductionFormula()
    {
        Formula body=All("n",Nat(),Imp(Lt(D(0),V("n")),Call("Good",V("n"))));
        foreach(var premise in new[]{"ExtraOK","MainBoxOK","ResidueTreeOK",
            "LargeLiftsOK","SmallLiftsOK","BaseOK"}) body=Imp(V(premise),body);
        return body;
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
