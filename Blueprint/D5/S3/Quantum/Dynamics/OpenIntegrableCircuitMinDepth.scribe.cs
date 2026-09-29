using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OpenIntegrableCircuitMinDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/garciafernandez2026openqc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the open-boundary integrable quantum circuits of Garcia Fernandez, Paletta and Retore, the least depth over the configurations with kappa of the N sites carrying -kappa is floor(N/(kappa + 1)) + 1 whenever 1 <= kappa and 2 kappa <= N.",
        H("The minimum depth of open integrable circuits"),
        Blocks(
            Node("result", "Minimum depth", ResultFormula(),
                "Read the circuit of a set S of sites as the path of sites 0, 1, ..., N, with site 0 for the boundary gate K1, site N for KN and site k in between for U_k: the circuit lists these gates in the order of the sites outside S decreasing, then 0, then the sites of S increasing, and two gates share a site of the chain exactly when their sites are consecutive. So the circuit fits in L layers exactly when some labelling of the sites 0, ..., N by numbers below L increases along each step from k to k + 1 with k + 1 in S and decreases along each other step. Along a run of consecutive steps outside S the labels decrease, and each of the |S| steps into S can raise the label by at most L - 1, which forces N < (|S| + 1) L; hence the depth is at least floor(N/(kappa + 1)) + 1. Conversely, cutting the sites 1, ..., N into kappa + 1 runs of length at most floor(N/(kappa + 1)) separated by the kappa sites of S gives a labelling below floor(N/(kappa + 1)) + 1, by induction on kappa.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("openqc-mindepth-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula ResultFormula()
    {
        Formula n = F.Id("N"), k = F.Id("kappa");
        return Disp(All("N", Naturals(), All("kappa", Naturals(), Implies(
            And(AtMost(D(1), k), AtMost(Times(D(2), k), n)),
            Equal(Call("minDepth", n, k), Add(new Formula.Floor(new Formula.Fraction(n, Add(k, D(1)))), D(1)))))));
    }
}
