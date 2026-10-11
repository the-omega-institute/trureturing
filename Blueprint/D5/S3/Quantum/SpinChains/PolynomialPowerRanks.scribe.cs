using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class PolynomialPowerRanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial normalized at a nilpotent specialization certifies every maximal power rank.",
        H("Polynomial certificates for power ranks"),
        Blocks(
            Paragraph(Text("Let K be any field, I a finite matrix index type with decidable equality, and S any type of variables. For a polynomial matrix A and a point x : S → K, write A(x) for the matrix obtained by evaluating every entry at x. No characteristic assumption or finiteness assumption on S is needed.")),
            Describe.Lean(
                DescribeId.Create("polynomial-power-ranks-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/PolynomialPowerRanks.exists_polynomial_power_rank_certificate"),
                H("One polynomial certifies all powers"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose the specialization at z is nilpotent with cutoff H and dominates the rank of every power at every point. There is a polynomial P whose value at z is one. At every point where P is nonzero, all power ranks agree with their values at z.")),
                    Paragraph(Text("For each r below H, put d equal to the rank of A(z) raised to r. Choose constant left and right matrices taking this power to rank normal form, with an identity block of size d. Lift their entries to constant polynomials and take the determinant of the corresponding block of the transformed polynomial power. Evaluation commutes with multiplication, powers, and determinants, so this determinant evaluates to one at z. A nonzero value gives a full-rank block, and the submatrix and product rank inequalities force rank at least d.")),
                    Paragraph(Text("The finite product of these determinants is P. Its value at z is one, and a nonzero product forces every factor to be nonzero. The assumed rank bound supplies the opposite inequality. For powers at least H, nilpotence makes the reference power zero, and the same bound forces rank zero at every point. Empty blocks have determinant one, so zero ranks and empty matrix index types are included."))),
                DescribeRole.Theorem)),
        []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Power(Formula x, Formula r) => new Formula.Power(Parenthesized(x), r);

    private static Formula Statement()
    {
        var k = F.Id("K"); var i = F.Id("I"); var s = F.Id("S");
        var a = F.Id("A"); var z = F.Id("z"); var h = F.Id("H");
        var x = F.Id("x"); var r = F.Id("r"); var p = F.Id("P");
        var type = Call("Type");
        var nats = Seq(Mathbb, Grp(F.Id("N")));
        var polynomial = Call("MvPolynomial", s, k);
        var point = Arrow(s, k);
        Formula MatrixAt(Formula t) => Call("map", a, Call("eval", t));
        Formula RankAt(Formula t) => Call("rank", Power(MatrixAt(t), r));
        var bounded = All("x", point, All("r", nats, Le(RankAt(x), RankAt(z))));
        var ranks = All("r", nats, Eq(RankAt(x), RankAt(z)));
        var locus = All("x", point, Implies(Ne(Call("eval", x, p), D(0)), ranks));
        var conclusion = Some("P", polynomial, And(Eq(Call("eval", z, p), D(1)), locus));
        var claim = Implies(And(Eq(Power(MatrixAt(z), h), D(0)), bounded), conclusion);
        var data = All("A", Call("Matrix", i, i, polynomial), All("z", point, All("H", nats, claim)));
        var instances = Assumption(Call("Field", k),
            Assumption(Call("Fintype", i), Assumption(Call("DecidableEq", i), data)));
        return All("K", type, All("I", type, All("S", type, instances)));
    }
}
