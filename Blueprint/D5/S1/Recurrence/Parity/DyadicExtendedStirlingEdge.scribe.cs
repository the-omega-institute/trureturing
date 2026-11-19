using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DyadicExtendedStirlingEdgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/kurkov2024a358612");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary-weight support and the factorial edge of the literal rational extended Stirling array.",
        H("The binary-weight row edge"),
        Blocks(
            Paragraph(Text("All indices range over the natural numbers, including zero. T is the literal rational scalar array of D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock; it is not defined by its edge values. The function wt is binary popcount from D5/S1/Digit/DyadicRowPolynomialRecurrence. The function a is exactly A284005 from D5/S1/Digit/KurkovWeightProductBinomial, with a(0)=1 and a(1)=2. Casts, division and array values in the edge identity are rational; factorial and its argument are natural.")),
            Node("support", "The support bound", All("n", All("k", Imp(
                new Formula.Relation(Add(Call("wt", V("n")), D(2)), FormulaRelationOperator.LessThan, V("k")),
                Eqn(Call("T", V("n"), V("k")), D(0))))),
                "Strong induction on the row uses its exact dyadic decomposition n=2^g(n)*(2*h(n)+1). The parent is strictly smaller, and wt(n)=wt(h(n))+1. Both parent columns in the block law are outside their support, so they vanish."),
            Node("result", "The complete row-edge identity", All("n", Eqn(
                Call("T", V("n"), Add(Call("wt", V("n")), D(2))),
                new Formula.Fraction(Call("rat", Call("a", V("n"))),
                    Call("rat", Call("factorial", Add(D(1), Call("wt", V("n")))))))),
                "This is the all-natural-row conjectured formula T(n,A000120(n)+2)=A341392(n) from A358612, using the A341392 definition A284005(n)/(1+A000120(n))!. The initial row is checked separately. At positive n the upper parent term vanishes by support; the remaining block coefficient is (wt(h(n))+2)^g(n). The source-owner identity a(n)=(wt(h(n))+2)^(g(n)+1)*a(h(n)) and factorial recursion finish the induction. The support statement is proved, not assumed. No bounded row restriction or integrality hypothesis is added. The scalar PARI source is used only on positive columns; the formal zero-column extension never enters the induction. The dyadic block law is a reused live prerequisite, without a separate block-problem settlement in this document. This statement does not assert integrality or any other A358612 conjecture.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a358612-row-edge"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("dyadic-extended-stirling-edge-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Seq(Mathbb, Grp(V("N"))), body);
}
