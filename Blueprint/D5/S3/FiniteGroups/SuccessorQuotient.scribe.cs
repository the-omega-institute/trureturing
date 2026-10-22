using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal static class SuccessorFormula
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

internal sealed class SuccessorQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = SuccessorFormula.V("V"); var r = SuccessorFormula.V("R");
        var k = SuccessorFormula.V("K"); var u = SuccessorFormula.V("u");
        Formula Context(Formula f) => SuccessorFormula.All("V", SuccessorFormula.Type,
            SuccessorFormula.All("R", SuccessorFormula.Rel(v), f));
        Formula FiniteContext(Formula f) => Context(SuccessorFormula.Imp(
            SuccessorFormula.And(SuccessorFormula.Call("Finite", v),
                SuccessorFormula.And(SuccessorFormula.Out(r), SuccessorFormula.In(r))), f));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The least successor-compatible quotient controls both assignments and all relation symmetries.",
            H("A canonical quotient of a directed relation"), Blocks(
                Paragraph(Text("The relation R may contain loops. An admissible equivalence puts all successors of one vertex in one class, "
                    + "and puts successors of equivalent vertices in equivalent classes. Intersecting all such equivalences gives the least one. "
                    + "PositiveOutdegree(R) means every x has some y with R(x,y); PositiveIndegree(R) means every y has some x with R(x,y). "
                    + "Positive outdegree defines the successor on its classes; positive indegree makes that successor onto. "
                    + "On a finite vertex type the successor is therefore a permutation beta.")),
                SuccessorFormula.Desc("SuccessorQuotient", "assignmentEquiv", "Exact descent of assignments",
                    Context(SuccessorFormula.All("K", SuccessorFormula.Type,
                        SuccessorFormula.All("u", SuccessorFormula.Arrow(k,k),
                            SuccessorFormula.Imp(SuccessorFormula.Out(r),
                                SuccessorFormula.Call("Equiv", SuccessorFormula.Call("Assignments",r,u),
                                    SuccessorFormula.Call("QuotientAssignments",r,u)))))),
                    "Assignments satisfy t(y)=u(t(x)) on every arrow x to y. Their equality relation is admissible directly from these equations. "
                    + "They consequently descend uniquely to the least quotient. Pullback is the inverse; no constancy hypothesis is assumed.",
                    DescribeRole.Definition),
                SuccessorFormula.Desc("SuccessorQuotient", "block_successor_commute", "Functorial successor",
                    Context(SuccessorFormula.Imp(SuccessorFormula.Out(r),
                        SuccessorFormula.All("g", SuccessorFormula.Call("relationAut",r),
                            SuccessorFormula.All("q", SuccessorFormula.Blocks(r),
                                SuccessorFormula.Eq(SuccessorFormula.Call("blockHom",r,SuccessorFormula.V("g"),
                                    SuccessorFormula.Call("successor",r,SuccessorFormula.V("q"))),
                                    SuccessorFormula.Call("successor",r,
                                        SuccessorFormula.Call("blockHom",r,SuccessorFormula.V("g"),SuccessorFormula.V("q")))))))),
                    "Every relation automorphism preserves the least equivalence and induces a permutation of its classes. This induced action commutes with the successor."),
                SuccessorFormula.Desc("SuccessorQuotient", "kernelRestriction", "The actual block-action kernel",
                    Context(SuccessorFormula.Arrow(SuccessorFormula.Call("ker",SuccessorFormula.Call("blockHom",r)),
                        SuccessorFormula.All("q",SuccessorFormula.Blocks(r),
                            SuccessorFormula.Call("Perm",SuccessorFormula.Call("Fiber",r,SuccessorFormula.V("q")))))),
                    "An element of the kernel preserves each actual fiber of the quotient map, so restriction defines a permutation of each fiber. "
                    + "These restrictions together determine the original permutation. The action on classes need not be faithful.", DescribeRole.Definition),
                SuccessorFormula.Desc("SuccessorQuotient", "relation_aut_joint_bound", "The centralizer and fiber bound",
                    FiniteContext(SuccessorFormula.Le(SuccessorFormula.Card(SuccessorFormula.Call("relationAut",r)),
                        SuccessorFormula.Mul(SuccessorFormula.Card(SuccessorFormula.Call("centralizer",SuccessorFormula.Call("beta",r))),
                            SuccessorFormula.Card(SuccessorFormula.Call("BlockPermutationProduct",r))))),
                    "Here BlockPermutationProduct is the dependent product, over quotient classes q, of the symmetric group on Fiber(R,q); "
                    + "centralizer(beta) is the centralizer of the singleton containing beta inside the symmetric group on Blocks(R). "
                    + "The image of the block action lies in this centralizer. Its kernel injects into the displayed product. "
                    + "Kernel times image gives the bound, retaining all block permutations.")), []));
    }
}
