using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SignedGraphSpectral;

internal sealed class HuHanSquareEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.";
    private static readonly LibraryNoteRef Signed =
        LibraryNoteRef.Create("D5/L/QuadraticForms/huhan2026signedsquareenergy");
    private static readonly LibraryNoteRef Unsigned =
        LibraryNoteRef.Create("D5/L/QuadraticForms/huliuwang2026squareenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two sharp equality classes of signed positive square energy.",
        H("Hu–Han Problem 6.1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both signed square-energy equality classes"),
                StatementSource.FromAuthor(Disp(Endpoints())),
                AssessedProvenance.FromRepo(Signed, Unsigned),
                Blocks(
                    Paragraph(Text(
                        "Part (i) states that s⁺ = 2m − n + 1 exactly for signed trees and "
                        + "balanced complete graphs. Part (ii) states that s⁺ = n − 1 exactly "
                        + "for signed trees and antibalanced complete graphs.")),
                    Paragraph(Text(
                        "Every finite vertex set can be labeled by Fin n. The signing assigns "
                        + "one Boolean to each unordered pair and signed adjacency uses its "
                        + "value only on actual edges. The positive square energy sums λ² over "
                        + "every strictly positive eigenvalue occurrence of that matrix. "
                        + "Balance and antibalance require all edge entries to be θᵢθⱼ and "
                        + "−θᵢθⱼ, respectively, for one vertex sign vector. These conditions "
                        + "describe the switching classes. The singleton has energy zero and "
                        + "satisfies both endpoint equalities.")),
                    Paragraph(Text(
                        "Hu–Han supply the sharp bounds and the conservation identity. "
                        + "Hu–Liu–Wang supply the unsigned equality classifications and the "
                        + "normalized clique decomposition. The signed proof extends zero-sum "
                        + "data across blocks, uses commutation with the positive spectral "
                        + "part to exclude attached cliques, and recovers the switching signs "
                        + "on a complete graph. Conservation transfers the upper classification "
                        + "to the lower one under reversal of every edge sign."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hu-han-2026-signed-square-energy-equality"),
                    ResolutionKind.Proved)))));

    private static Formula Endpoints()
    {
        var n = F.Id("n");
        var graph = F.Id("G");
        var signing = F.Id("sigma");
        var vertices = Call("Fin", n);
        var edgeCount = Call("edgeCount", graph);
        var energy = Call("sPlus", graph, signing);
        var upperBound = new Formula.Binary(
            new Formula.Binary(new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, edgeCount),
                FormulaBinaryOperator.Subtract, n),
            FormulaBinaryOperator.Add, D(1));
        var lowerBound = new Formula.Binary(n, FormulaBinaryOperator.Subtract, D(1));

        Formula Clause(Formula bound, string signPattern) => Logic(
            new Formula.Relation(energy, FormulaRelationOperator.Equal, bound),
            FormulaLogicOperator.Iff,
            Logic(Call("IsTree", graph), FormulaLogicOperator.Or,
                Logic(Call("Complete", graph), FormulaLogicOperator.And,
                    Call(signPattern, graph, signing))));

        var clauses = Logic(Clause(upperBound, "Balanced"), FormulaLogicOperator.And,
            Clause(lowerBound, "Antibalanced"));
        return All("n", F.Id("Nat"), All("G", Call("SimpleGraph", vertices),
            All("sigma", new Formula.TypeArrow(Call("Sym2", vertices), F.Id("Bool")),
                Logic(Call("Connected", graph), FormulaLogicOperator.Implies, clauses))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
