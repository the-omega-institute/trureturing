using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;
internal sealed class LyndonFactorChristoffelScanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/LyndonFactorChristoffelScan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/glensimpsonsmyth2017lyndonfactors");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scan gives the finite-index Lyndon factor set and count used in the Christoffel refutation.",
        H("Lyndon scans for the Christoffel factor count"), Blocks(
        N("factorScan_eq_occurrence_image", "The original occurrence image", WordParameters(Equal(Call("factorScan", Call("List.map", F.Id("w"), Call("List.finRange", F.Id("n")))), Call("Finset.image", Lam(F.Id("p"), Seq(Nats(), Times, Nats()), Call("factor", F.Id("w"), Proj(F.Id("p"), D(1)), Proj(F.Id("p"), D(2)))), Call("lyndonOccurrences", F.Id("w"))))), "For every sigma,n and w : Fin n -> Fin sigma, the scan set equals the image sending each valid pair (i,l) in lyndonOccurrences w to factor w i l. The proof reconstructs a valid slice from an arbitrary contiguous occurrence; its nonemptiness gives l>=1 and its enclosing word gives i+l<=n.", DescribeRole.Theorem),
        N("distinctLyndon_eq_scan", "The original distinct count", WordParameters(Equal(Call("distinctLyndon", F.Id("w")), Call("Finset.card", Call("factorScan", Call("List.map", F.Id("w"), Call("List.finRange", F.Id("n"))))))), "The original distinctLyndon count is exactly the cardinality of the scan set. This is an equality of the actual factor objects, with no count recurrence or occurrence-count replacement.", DescribeRole.Theorem),
        Paragraph(Text("The equalities relate the scan to the factor objects in the Christoffel refutation. The scan applies to finite words over Fin sigma, including the empty word. Its cardinality counts equal strings once.")))));
    private static DocumentBlock N(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Node(name, title, Disp(formula), prose, AssessedProvenance.FromRepo(Source), role);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("lyndon-transport-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lam(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Proj(Formula p, Formula digit) => Seq(p, Dot, digit);
    private static Formula WordParameters(Formula body)
    {
        Formula sigma = SigmaLower, n = F.Id("n"), w = F.Id("w");
        return All(sigma, Nats(), All(n, Nats(), All(w, Fn(Fin(n), Fin(sigma)), body)));
    }
}
