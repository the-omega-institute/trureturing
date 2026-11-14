using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA176605FiveTermRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2016a176605");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula SumOf(params Formula[] fs) => fs.Aggregate(Add);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula AtLeast(Formula n, int k) =>
        new Formula.Relation(Num(k), FormulaRelationOperator.LessThanOrEqual, n);
    private static Formula Cast(Formula x) => Par(Seq(x, Colon, Z));
    private static Formula SourceConditions(string sequence)
    {
        Formula m = F.Id("m"), p = F.Id("p");
        Formula convolution = Seq(new Formula.Subscript(F.Sum,
            Seq(p, InMacro, Call("range", Add(m, Num(1))))),
            Product(Call(sequence, p), Call(sequence, Subtract(m, p))));
        return And(Equal(Call(sequence, Num(0)), Num(1)),
            And(Equal(Call(sequence, Num(1)), Num(1)),
                All("m", Nat, Implies(AtLeast(m, 1),
                    Equal(Call(sequence, Add(m, Num(1))), Add(convolution, Num(1)))))));
    }
    private static Formula Statement()
    {
        Formula n = F.Id("n"), zn = Cast(n);
        Formula An(int lag) => Cast(Call("a", lag == 0 ? n : Subtract(n, Num(lag))));
        Formula equation = Equal(SumOf(Product(Par(Add(zn, Num(1))), An(0)),
            Product(Num(2), Par(Add(Product(new Formula.Negate(Num(3)), zn), Num(1))), An(1)),
            Product(Par(Subtract(Product(Num(9), zn), Num(13))), An(2)),
            Product(Num(8), Par(Add(new Formula.Negate(zn), Num(3))), An(3)),
            Product(Num(4), Par(Subtract(zn, Num(4))), An(4))), Num(0));
        return All("a", Seq(Nat, Sp, To, Sp, Nat), Implies(SourceConditions("a"),
            All("n", Nat, Implies(AtLeast(n, 4), equation))));
    }
    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a176605-" + name), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original A176605 nonlinear convolution satisfies Mathar's five-term identity at every legal backshift index.",
        H("Mathar's A176605 five-term identity"),
        Blocks(
            Node("source", "An actual source sequence", SourceConditions("source"),
                AssessedProvenance.FromLiterature(Source),
                "The natural-valued sequence is constructed by well-founded recursion: source(0)=source(1)=1, "
                + "and the displayed convolution defines source(m+1) only for m ≥ 1. Each referenced index is "
                + "strictly below m+1. The compiled Reg source_conditions proof verifies all these conditions, "
                + "and changed_law uses this actual sequence to establish full-family variation. Thus the "
                + "universal implication has an inhabited source domain. No recurrence at m=0 is imposed.", DescribeRole.Definition),
            Node("claim", "The full source question", new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Statement()),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A176605, revision 19, NAME specializes k=0 and l=1 in its nonlinear convolution. "
                + "FORMULA attributes the five-term conjecture to R. J. Mathar. The source omits the linear "
                + "onset. Here n ≥ 4 is the disclosed nonnegative-backshift interpretation, independent of "
                + "OFFSET 0,3. Every lag index is natural; every signed coefficient and sequence value in "
                + "the identity is evaluated in the integers after casting. All source sequences and all "
                + "n ≥ 4 are included. The source's generating-function and finite-sum assertions are not hypotheses.", DescribeRole.Definition),
            Node("result", "The complete five-term identity", Statement(), AssessedProvenance.FromRepo(Source),
                "For A=Σ a(n)X^n in Q[[X]], coefficient extensionality and the original convolution prove "
                + "F=X(1-X)A²-(1-X)A+1-X+X²=0, with the first two coefficients treated separately. "
                + "Differentiate F and multiply by X. Polynomial elimination then gives P(XA')+QA=R, "
                + "where P=1-6X+9X²-8X³+4X⁴, Q=1-4X+5X² and R=1-2X+4X²-2X³. "
                + "The eliminated factor 2XA-1 has constant coefficient -1 and is nonzero; the formal "
                + "power-series ring is a domain. The frozen A308815DFiniteRecurrence.euler_coeff and "
                + "four coefficient shifts give exactly the displayed relation because coeff(n,R)=0 "
                + "for n ≥ 4. No analytic convergence, assumed generating function or finite-prefix "
                + "replacement is used. The proof is classified bind-only under the external named-problem "
                + "resolution basis of issue #30568. No worldwide openness, priority or sibling resolution is asserted.",
                DescribeRole.Theorem))));
}
