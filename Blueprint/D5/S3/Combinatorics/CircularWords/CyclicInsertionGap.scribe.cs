using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class CyclicInsertionGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/CyclicInsertionGap.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a new label from an oriented circular word classifies all possible insertions by a unique actual gap.",
        H("Cyclic Insertion Gaps"),
        Blocks(
            Paragraph(Text(
                "Let A be any type with decidable equality, B a nonempty list with no repeated labels, "
                + "and x a label absent from B. Circular words identify lists under rotation and retain orientation. "
                + "For j in Fin(length(B)), gapCircle(B,x,j) is the rotation class of x followed by rotate(B,j). "
                + "Thus j records the gap immediately before the jth entry of B. Deleting x filters it from "
                + "the circular word. No walk, chosen component or restriction to some gaps is assumed.")),
            Describe.Lean(DescribeId.Create("complete-deletion-fiber"),
                DeclarationHandle.Create(Prefix + "gapCircle_fiber"),
                H("Every Oriented Insertion Has Exactly One Gap"),
                StatementSource.FromAuthor(FiberFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An oriented circular word C has distinct labels, contains x and has deletion residual B "
                    + "if and only if C equals gapCircle(B,x,j) for exactly one j. To obtain the gap, rotate a "
                    + "representative of C until x is first. Removing x leaves a rotation of B. Uniqueness "
                    + "uses the fact that x appears once: two representatives beginning with x cannot differ "
                    + "by a nonzero rotation. The remaining lists are therefore equal, and rotation indices "
                    + "of a nonempty list with distinct labels are equal modulo its length. Conversely, "
                    + "every displayed insertion has distinct labels, contains x and deletes to B."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "In a construction that deletes several selected labels from an actual permutation, apply "
                + "this result to the oriented circular word after the earlier deletions. It classifies every "
                + "child base by the newly selected label's actual gap, so vertex-domain coverage can be "
                + "established before constructing paths. A reversed residual must be treated with its own "
                + "orientation. The result does not prove a Hamilton cycle or any endpoint pairing.")))));

    private static Formula FiberFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), x = F.Id("x"), c = F.Id("C"), j = F.Id("j"), k = F.Id("k");
        Formula indices = Call("Fin", Call("length", b));
        Formula hypotheses = And(Call("Nodup", b), And(new Formula.Not(Seq(Open, Equal(b, Call("nil")), Close)), new Formula.Not(Seq(Open, Member(x, b), Close))));
        Formula fiber = And(Call("Nodup", c), And(Member(x, c), Equal(Call("delete", x, c), Call("coeCycle", b))));
        Formula atJ = Equal(c, Call("gapCircle", b, x, j));
        Formula uniqueness = All("k", indices, Implies(Equal(c, Call("gapCircle", b, x, k)), Equal(k, j)));
        Formula gap = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("j"), indices, And(atJ, uniqueness));
        return Disp(All("A", Call("Type"), Seq(OpenBracket, Call("DecidableEq", a), CloseBracket, Sp,
            All("B", Call("List", a), All("x", a, All("C", Call("Cycle", a),
                Implies(hypotheses, Iff(fiber, gap))))))));
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
