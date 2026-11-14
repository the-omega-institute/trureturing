using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SelfPowerCubicRemaindersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/SelfPowerCubicRemainders.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/englander2020a081215");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All six branches of Englander Conjecture XIV hold for the exact quotient at every integer index greater than two.", H("The six cubic least remainders"), Blocks(
            Describe.Lean(DescribeId.Create("self-power-selfpowercubicremainders-twicer"),
                DeclarationHandle.Create(Prefix + "twiceR"), H("The six prescribed polynomials"),
                StatementSource.FromAuthor(Disp(TwiceFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The branch is selected by the natural residue n modulo six. Every displayed polynomial is evaluated in the integers. These are exactly twice the remainders on physical page 63; using twice the remainder keeps integrality explicit."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowercubicremainders-tail-blocks"),
                DeclarationHandle.Create(Prefix + "tail_blocks"), H("Uniform weighted-sum descent"),
                StatementSource.FromAuthor(Disp(BlocksFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Split the finite double sum into two consecutive blocks. For Q=y^3+1 and S=1+y+y^2, the six-step difference T(m+6,y)-T(m,y)-3S is divisible by Q. Induction gives the displayed statement for every h, t and integer y, without a restriction on t. This is the unbounded step used by the residue proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("self-power-selfpowercubicremainders-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The full cubic claim"),
                StatementSource.FromAuthor(Disp(Iff(Call("claim"), ClaimFormula()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both conjuncts apply for every natural n greater than two. The first establishes the exact original quotient; the second identifies twice its least nonnegative integer remainder modulo n cubed minus one. This is equivalent to the printed integer domain and all six branch equalities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowercubicremainders-result"),
                DeclarationHandle.Create(Prefix + "result"), H("All six least-remainder branches"),
                StatementSource.FromAuthor(Disp(ClaimFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Write n=6h+c with 0<=c<6. Apply the block descent at t=c+1 and y=-n. The six integral representatives are 108h^3+18h^2-3h, 108h^3+18h^2+3h, 108h^3+162h^2+69h+8, 108h^3+126h^2+45h+5, 108h^3+234h^2+171h+41 and 108h^3+270h^2+225h+62. The proof shows directly that the quotient minus the representative is divisible by the modulus, and that the representative lies in the half-open interval from zero to the modulus. Uniqueness of Euclidean remainder then applies. Polynomial expansion gives twiceR. No division by two in a residue ring or coprimality assumption is used."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("englander-a081215-xiv-cubic-remainders"), ResolutionKind.Proved)))));
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [..args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Cast(Formula a, Formula t) => Par(Seq(a, Colon, Sp, t));
    private static Formula Mod(Formula a, Formula m) => Call("emod", a, m);
    private static Formula Den(Formula n) => Pow(Seq(Cast(n, Int()), Plus, D(1)), D(2));

    private static Formula Branch(int c)
    {
        var z = Cast(V("n"), Int()); var cube = Pow(z, D(3)); var square = Pow(z, D(2));
        return c switch {
            0 => Seq(cube, Plus, square, Minus, z),
            1 => Seq(cube, Minus, D(2), Star, square, Plus, D(2), Star, z, Minus, D(1)),
            2 => Seq(cube, Plus, D(3), Star, square, Minus, z, Minus, D(2)),
            3 => Seq(cube, Minus, D(2), Star, square, Plus, D(1)),
            4 => Seq(cube, Plus, square, Plus, z, Minus, D(2)),
            _ => Seq(cube, Minus, D(1)) };
    }
    private static Formula TwiceFormula()
    {
        Formula? all = null;
        for (int c = 0; c < 6; c++) {
            Formula digit = c switch { 0 => D(0), 1 => D(1), 2 => D(2), 3 => D(3), 4 => D(4), _ => D(5) };
            var branch = Imp(Eqn(Call("mod", V("n"), D(6)), digit), Eqn(Call("twiceR", V("n")), Branch(c)));
            all = all is null ? branch : And(all, branch);
        }
        return All("n", Nat(), all!);
    }
    private static Formula ClaimFormula() => All("n", Nat(), Imp(Lt(D(2), V("n")),
        And(Eqn(Seq(Den(V("n")), Star, Call("a", V("n"))), Call("numerator", V("n"))),
            Eqn(Seq(D(2), Star, Mod(Call("a", V("n")), Seq(Pow(Cast(V("n"), Int()), D(3)), Minus, D(1)))), Call("twiceR", V("n"))))));

    private static Formula BlocksFormula()
    {
        var h = V("h"); var t = V("t"); var y = V("y");
        var sum = Par(Seq(D(1), Plus, y, Plus, Pow(y, D(2))));
        var comparison = Par(Seq(D(3), Star, Cast(h, Int()), Star, sum, Plus, Call("tail", t, y)));
        var index = Seq(D(6), Star, h, Plus, t);
        var difference = Par(Seq(Call("tail", index, y), Minus, comparison));
        var divides = new Formula.Relation(Seq(Pow(y, D(3)), Plus, D(1)), FormulaRelationOperator.Divides, difference);
        return All("h", Nat(), All("t", Nat(), All("y", Int(), divides)));
    }
}
