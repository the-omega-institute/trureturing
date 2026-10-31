using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungPolynomialGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous coordinates of Young multiplicities", H("Complete homogeneous coordinates of Young multiplicities"), Blocks(
            Paragraph(Text("The polynomial hsymmPart(sigma,R,nu) is the product of complete homogeneous symmetric polynomials for the positive parts of nu. psumPart(sigma,R,rho) is the product of power sums for every part of rho, including ones. fixedTabloids(n,nu,pi) counts the cosets of the literal Young subgroup of nu fixed by pi. A fibre preserving permutation is an independent permutation of each fibre. Summing stabilizer orders over every colouring of a given fibre size contributes n factorial. Applying that count to colourings by pairs proves the displayed averaging identity for every commutative semiring and finite alphabet. partWeight(sigma,xi) is the existing sorted exponent vector, transported through Fintype.equivFin. Multiplicity(mu,nu) is the actual complex dimension of Hom from the preserved same-shape complex polytabloid representation to the Young permutation representation. When the alphabet records xi, reading its coefficient in the averaging identity and cancelling n factorial gives the Gram entry of those actual multiplicities. The alphabet condition is only the number of positive parts of xi; the degree may be arbitrarily large.")),
            Describe.Lean(DescribeId.Create("sum-card-fixedpoints-smul-psumpart-partition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungPolynomialGram.sum_card_fixedPoints_smul_psumPart_partition"),
                H("Averaging the Young permutation character"), StatementSource.FromAuthor(Average()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coeff-hsymmpart-partweight-eq-sum-multiplicity-mul"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungPolynomialGram.coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul"),
                H("The homogeneous coefficient is the actual multiplicity Gram entry"), StatementSource.FromAuthor(Coefficient()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Open, b, Close);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Open, body, Close);
    private static Formula Nat() => Call("Nat");
    private static Formula Complex() => Call("Complex");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Perm(Formula n) => Call("Perm", Call("Fin", n));

    private static Formula Inst(string name, Formula x) => Seq(OpenBracket, Call(name, x), CloseBracket, Comma, Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula M(Formula mu, Formula nu) => Call("complexNatCast", Call("Multiplicity", mu, nu));
    private static Formula Average()
    {
        Formula n = Id("n"), sigma = Id("sigma"), ring = Id("R"), nu = Id("nu"), pi = Id("pi");
        Formula equation = Eq(SumOver("pi", Perm(n), Call("nsmul", Call("fixedTabloids", n, nu, pi),
            Call("psumPart", sigma, ring, Call("partition", pi)))), Call("nsmul", Call("factorial", n),
                Call("hsymmPart", sigma, ring, nu)));
        return Disp(All("sigma", Seq(Call("Type"), Star), Seq(Inst("Fintype", sigma),
            Inst("DecidableEq", sigma), All("R", Seq(Call("Type"), Star), Seq(Inst("CommSemiring", ring),
                All("n", Nat(), All("nu", Part(n), equation)))))));
    }
    private static Formula Coefficient()
    {
        Formula n = Id("n"), sigma = Id("sigma"), nu = Id("nu"), xi = Id("xi"), mu = Id("mu");
        Formula premise = new Formula.Relation(Call("card", Call("parts", xi)),
            FormulaRelationOperator.LessThanOrEqual, Call("FintypeCard", sigma));
        Formula equation = Eq(Call("coeff", Call("hsymmPart", sigma, Complex(), nu), Call("partWeight", sigma, xi)),
            SumOver("mu", Part(n), Mul(M(mu, nu), M(mu, xi))));
        return Disp(All("sigma", Seq(Call("Type"), Star), Seq(Inst("Fintype", sigma),
            All("n", Nat(), All("nu", Part(n), All("xi", Part(n), Imp(premise, equation)))))));
    }

}
