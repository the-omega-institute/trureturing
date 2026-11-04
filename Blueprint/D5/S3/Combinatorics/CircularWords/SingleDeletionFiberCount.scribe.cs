using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class SingleDeletionFiberCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-support oriented cycle has exactly one legal source for each insertion gap, so a labelled single-deletion fibre has cardinality A.card - 1.",
        H("Exact Single-Deletion Fibre Count"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite support in an arbitrary ambient type with decidable equality. "
                + "The carrier is the native Mathlib Cycle quotient: rotation classes are identified and reversal remains distinct. "
                + "Fix x in A and a nodup residual cycle B whose support is A.erase x. The fibre consists of actual original cycles C "
                + "with C.Nodup, C.toFinset = A, and the labelled deletion delete x C equal to B.")),
            Describe.Lean(DescribeId.Create("insertion-equivalence"),
                DeclarationHandle.Create(Prefix + "insertionEquiv"),
                H("Insertion Slots Are the Exact Fibre"), StatementSource.FromAuthor(InsertionFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Choose any nodup list representative L of B. For j in Fin L.length, gapCircle L x j inserts x immediately before "
                    + "the jth residual entry after rotating L; j = 0 is the cyclic cut before L[0]. Every displayed cycle is nodup, "
                    + "has exactly support A, and deletes to B. The existing gapCircle_fiber theorem supplies a unique slot for every "
                    + "legal source cycle. Anchored injectivity together with nodup rotation uniqueness proves that two slots cannot give "
                    + "the same rotation class, so the equivalence counts actual cycles rather than chosen representatives."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("deletion-fibre-card"),
                DeclarationHandle.Create(Prefix + "deletion_fiber_card"),
                H("The Fibre Has Cardinality A.card Minus One"), StatementSource.FromAuthor(CardFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a residual cycle B supported on A.erase x, choose a representative L. Nodup support gives "
                    + "L.length = (A.erase x).card = A.card - 1. Transporting Nat.card across insertionEquiv therefore yields the exact "
                    + "cardinality of the subtype of original rotation classes. The statement is valid for every ambient type; it assumes "
                    + "no Fintype α and makes no probability, enumeration, optimum, or novelty claim."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The fibre includes every insertion slot, including the wrap-around cut, and keeps the source support and orientation exact. "
                + "A transient SupportedCircle application can use the same equivalence, but the canonical result is the two reusable "
                + "declarations above.")))));

    private static Formula InsertionFormula()
    {
        Formula t = F.Id("T"), A = F.Id("A"), x = F.Id("x"), B = F.Id("B"), C = F.Id("C"), j = F.Id("j");
        Formula support = And(Call("Nodup", C), And(Eq(Call("toFinset", C), A), Eq(Call("delete", x, C), Call("coeCycle", B))));
        Formula fiber = Call("Subtype", support);
        Formula equiv = Call("Equiv", Call("Fin", Call("length", B)), fiber);
        Formula premise = And(In(x, A), And(Call("Nodup", B), And(Ne(B, Call("nil")), Eq(Call("toFinset", B), Call("erase", x, A)))));
        Formula quantified = All("A", Call("Finset", t), All("x", t, All("B", Call("List", t), Imp(premise, equiv))));
        return WithType(quantified);
    }

    private static Formula CardFormula()
    {
        Formula t = F.Id("T"), A = F.Id("A"), x = F.Id("x"), B = F.Id("B"), C = F.Id("C");
        Formula fiber = Call("Subtype", And(Call("Nodup", C),
            And(Eq(Call("toFinset", C), A), Eq(Call("delete", x, C), B))));
        Formula premise = And(Le(D(3), Call("card", A)), And(In(x, A), And(Call("Nodup", B), Eq(Call("toFinset", B), Call("erase", x, A)))));
        Formula equality = Eq(Call("NatCard", fiber), Sub(Call("card", A), D(1)));
        Formula quantified = All("A", Call("Finset", t), All("x", t, All("B", Call("Cycle", t), Imp(premise, equality))));
        return WithType(quantified);
    }

    private static Formula WithType(Formula body) => Disp(All("T", Call("Type"),
        Seq(OpenBracket, Call("DecidableEq", F.Id("T")), CloseBracket, Sp, body)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Not(Seq(Open, Eq(left, right), Close));
    private static Formula In(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
