using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Coloring;

internal sealed class KrebsC12SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/krebsleyva2025ranktwo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-three standardized Abelian Cayley graphs can contain four-cliques at unbounded row counts.",
        H("Krebs–Leyva Conjecture 1.2"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The fixed-rank stabilization conjecture"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 1.2 is on printed page 3 of arXiv:2511.03028v1. The rank is the " +
                        "number of columns. The threshold m₀ can depend on the positive rank r. " +
                        "At every row count m at or above that threshold, the implication ranges " +
                        "over all integer matrices of size m by r.")),
                    Paragraph(Text(
                        "The vertices of the source graph are the cosets of the integer span " +
                        "of the matrix columns. Its generator set consists of the two signs " +
                        "of each standard coordinate coset. Zero in that set is exactly the " +
                        "loop condition. Bipartiteness means looplessness and two-colorability " +
                        "of the simple Cayley graph. The source chromatic number has value " +
                        "infinity when a loop occurs and otherwise is the Mathlib chromatic number."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A rank-three family with four-cliques"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At row count 4(k + 1) + 3 the three columns are e₂ − 2e₁, e₃ − 3e₁, " +
                        "and 4e₁ + Σⱼ j fⱼ, where fⱼ denotes the jth additional coordinate and " +
                        "1 ≤ j ≤ 4(k + 1). Each row is nonzero. If a coordinate vector were " +
                        "a column combination, its first five row equations would force all " +
                        "three coefficients to be zero, which contradicts its unit entry. " +
                        "Thus both signs of every coordinate coset are nonzero.")),
                    Paragraph(Text(
                        "In the quotient the first two columns give [e₂] = 2[e₁] and " +
                        "[e₃] = 3[e₁]. The four vertices 0, [e₁], 2[e₁], 3[e₁] are pairwise " +
                        "adjacent because each positive-index difference is a nonzero coordinate " +
                        "generator. The graph therefore fails two-colorability and has chromatic " +
                        "number at least four. Taking k = m₀ supplies a witness past every " +
                        "proposed threshold at rank three."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krebs-leyva-2025-conjecture-1-2"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        var r = F.Id("r");
        var m = F.Id("m");
        var threshold = F.Id("m0");
        var matrix = F.Id("M");
        var i = F.Id("i");
        var j = F.Id("j");
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var integers = Seq(Mathbb, Grp(F.Id("Z")));
        var matrixType = new Formula.Power(integers, Seq(m, Sp, Times, Sp, r));
        var nonzeroRows = Bind(FormulaQuantifier.ForAll, "i", Call("Fin", m),
            Bind(FormulaQuantifier.Exists, "j", Call("Fin", r),
                Rel(new Formula.Apply(matrix, [i, j]), FormulaRelationOperator.NotEqual, D(0))));
        var conclusion = Imp(nonzeroRows, Imp(new Formula.Not(Call("IsBipartite", matrix)),
            Imp(new Formula.Not(Call("HasLoops", matrix)),
                Rel(Call("chromaticNumber", matrix), FormulaRelationOperator.Equal, D(3)))));
        return new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Bind(FormulaQuantifier.ForAll, "r", nat,
                Imp(Rel(D(0), FormulaRelationOperator.LessThan, r),
                    Bind(FormulaQuantifier.Exists, "m0", nat,
                        Bind(FormulaQuantifier.ForAll, "m", nat,
                            Imp(Rel(threshold, FormulaRelationOperator.LessThanOrEqual, m),
                                Bind(FormulaQuantifier.ForAll, "M", matrixType, conclusion)))))));
    }

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
