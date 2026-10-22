using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal static class PowerAssignmentFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    internal static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Type => V("Typeu");
    internal static Formula Rel(Formula v) => new Formula.TypeArrow(v, new Formula.TypeArrow(v, V("Prop")));
    internal static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Card(Formula t) => Call("card", t);
    internal static Formula Blocks(Formula r) => Call("Blocks", r);
    internal static Formula Out(Formula r) => Call("PositiveOutdegree", r);
    internal static Formula In(Formula r) => Call("PositiveIndegree", r);
    internal static DocumentBlock.Describe Desc(string module, string name, string title,
        Formula f, string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/" + module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            StrataLint.Scribe.DefinitionDsl.Blocks(Paragraph(Text(text))), role);
}


internal sealed class SuccessorPowerAssignmentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q=PowerAssignmentFormula.V("Q"); var k=PowerAssignmentFormula.V("K"); var b=PowerAssignmentFormula.V("beta");
        Formula Context(Formula f) => PowerAssignmentFormula.All("Q",PowerAssignmentFormula.Type,
            PowerAssignmentFormula.All("K",PowerAssignmentFormula.Type,
                PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Field",k),
                    PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Finite",q),
                        PowerAssignmentFormula.All("beta",PowerAssignmentFormula.Call("Perm",q),f)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Squaring-compatible unit assignments are finite, and their exact cardinality is the product of the successor-cycle root factors.",
            H("Root factors of successor cycles"), Blocks(
                Paragraph(Text("SquareAssignments(beta) consists of functions v from Q to the units of the field K satisfying v(beta(q))=v(q)^2. "
                    + "Iteration gives v(beta^j(q))=v(q)^(2^j). A return of length l therefore forces v(q)^(2^l-1)=1.")),
                PowerAssignmentFormula.Desc("SuccessorPowerAssignments","square_assignments_finite","Finiteness before cardinality",
                    Context(PowerAssignmentFormula.Call("Finite",PowerAssignmentFormula.Call("SquareAssignments",k,b))),
                    "The order of a finite permutation is positive and is a common return time. Evaluation embeds the assignment type into a finite product "
                    + "of groups of roots of unity. This proves finiteness independently of any natural-cardinality bound."),
                PowerAssignmentFormula.Desc("SuccessorPowerAssignments","cycleWeight","The cycle root product",
                    PowerAssignmentFormula.All("Q",PowerAssignmentFormula.Type,
                        PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Finite",q),
                            PowerAssignmentFormula.All("beta",PowerAssignmentFormula.Call("Perm",q),
                                PowerAssignmentFormula.Eq(PowerAssignmentFormula.Call("cycleWeight",b),PowerAssignmentFormula.Call("CycleRootProduct",b))))),
                    "CycleRootProduct is the product over Mathlib cycleFactorsFinset of 2 raised to the support cardinality of the cycle, minus one. "
                    + "The omitted fixed-point cycles have length one and factor one. No cycle partition of a larger ambient vertex set is substituted.",DescribeRole.Definition),
                PowerAssignmentFormula.Desc("SuccessorPowerAssignments","cycleEvaluationEquiv","Independent cycle-root realization",
                    PowerAssignmentFormula.All("Q",PowerAssignmentFormula.Type,
                        PowerAssignmentFormula.All("K",PowerAssignmentFormula.Type,
                            PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Field",k),
                                PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Fintype",q),
                                    PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("DecidableEq",q),
                                        PowerAssignmentFormula.All("beta",PowerAssignmentFormula.Call("Perm",q),
                                            PowerAssignmentFormula.Call("Equiv",PowerAssignmentFormula.Call("SquareAssignments",k,b),
                                                PowerAssignmentFormula.Call("CycleRootTuples",k,b)))))))),
                    "CycleRootTuples(K,beta) is the dependent product, over c in beta.cycleFactorsFinset, of rootsOfUnity(2^card(support(c))-1,K). "
                    + "Choose one representative in each nontrivial cycle. Evaluation records the value there. To realize a tuple, put z^(2^j) at "
                    + "position j in its cycle and one off that cycle, then multiply these disjoint contributions. The root equation proves wraparound, "
                    + "and disjoint supports give both inverse laws. This is a genuine equivalence over every field, including the empty carrier.",DescribeRole.Definition),
                PowerAssignmentFormula.Desc("SuccessorPowerAssignments","square_assignments_cycle_card","Exact complex cycle factors",
                    PowerAssignmentFormula.All("Q",PowerAssignmentFormula.Type,
                        PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Fintype",q),
                            PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("DecidableEq",q),
                                PowerAssignmentFormula.All("beta",PowerAssignmentFormula.Call("Perm",q),
                                    PowerAssignmentFormula.Eq(PowerAssignmentFormula.Card(PowerAssignmentFormula.Call("SquareAssignments",PowerAssignmentFormula.V("Complex"),b)),
                                        PowerAssignmentFormula.Call("CycleRootProduct",b)))))),
                    "For every finite decidable Q and every permutation beta, the equivalence gives exact cardinality. "
                    + "Complex.card_rootsOfUnity gives 2^l-1 for each cycle of length l; fixed points have the unique value one. "
                    + "There is no surjectivity hypothesis on evaluation or independent realizability: both inverse laws are proved in cycleEvaluationEquiv."),
                PowerAssignmentFormula.Desc("SuccessorPowerAssignments","square_assignments_weight_card","The exact cycle root cardinality",
                    PowerAssignmentFormula.All("Q",PowerAssignmentFormula.Type,
                        PowerAssignmentFormula.Imp(PowerAssignmentFormula.Call("Finite",q),
                            PowerAssignmentFormula.All("beta",PowerAssignmentFormula.Call("Perm",q),
                                PowerAssignmentFormula.Eq(PowerAssignmentFormula.Card(PowerAssignmentFormula.Call("SquareAssignments",PowerAssignmentFormula.V("Complex"),b)),
                                    PowerAssignmentFormula.Call("cycleWeight",b))))),
                    "Evaluation and realization are inverse bijections. For a root z on a cycle of length l, the coordinate at position k is z^(2^k). "
                    + "The equation z^(2^l-1)=1 gives exactly the wraparound relation. Independent cycle assignments are multiplied pointwise; disjoint supports "
                    + "ensure that evaluation recovers each chosen root separately. Fixed-point coordinates equal one, so singleton cycles contribute mu_1={1}. "
                    + "Complex.card_rootsOfUnity counts every nontrivial cycle factor exactly. The cycles belong to the successor permutation itself.")), []));
    }
}
