using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaProductPartitionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2022a356508");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's OEIS A356508 product equation and its coefficient residues modulo four.",
        H("Hanna's product-partition congruence"),
        Blocks(
            Paragraph(Text(
                "The source is P. D. Hanna's OEIS A356508 entry. It states verbatim: "
                    + "G.f. A(x) satisfies: 2 = Product_{n>=1} (1 + x^n*A(x)) * "
                    + "(1 + x^(n-1)/A(x)). Its comment conjectures verbatim: "
                    + "a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd "
                    + "number of partitions (A052002), otherwise a(n) == 0 (mod 4) "
                    + "when n > 0.")),
            Paragraph(Text(
                "PowerSeries is the formal power-series type, X is its indeterminate, "
                    + "coeff and constantCoeff read coefficients, and invOfUnit is the "
                    + "formal inverse determined by the nonzero constant coefficient. "
                    + "Products are coefficientwise finite windows; Nat.Partition and "
                    + "Fintype.card give the ordinary partition number.")),
            Node("IsGF", "The coefficientwise product equation", IsGFFormula(),
                "The displayed predicate is the source generating-function equation over "
                    + "rational formal power series, with each coefficient represented by "
                    + "the finite window through index m+1.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's coefficient-residue conjecture", ClaimFormula(),
                "The displayed proposition includes existence of a rational solution and "
                    + "the source's integer-coefficient and modulo-four assertions for every "
                    + "positive coefficient.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A356508 conjecture", ClaimBody(),
                "Integral coefficient contraction gives the unique solution. Mapping the "
                    + "fixed-point equation to ZMod 4, the candidate "
                    + "2 times the partition series in X squared minus one squares to one; "
                    + "the paired product therefore reduces to the reciprocal partition "
                    + "identity. Its coefficient formula is 2 times the ordinary partition "
                    + "number at n/2 for even n and zero for odd n, which gives the two "
                    + "residue cases.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a356508-hanna-product-partition-mod-four"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a356508-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);

    private static Formula Nat() => F.Id("Nat");
    private static Formula Int() => F.Id("Int");
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula PS(Formula ring) => Call("PowerSeries", ring);
    private static Formula A() => F.Id("A");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula K() => F.Id("k");
    private static Formula Z() => F.Id("z");
    private static Formula X() => QCall("PowerSeries", "X");
    private static Formula Coeff(Formula n, Formula a) => QCall("PowerSeries", "coeff", n, a);
    private static Formula Constant(Formula a) => QCall("PowerSeries", "constantCoeff", a);
    private static Formula Inverse(Formula a) => QCall("PowerSeries", "invOfUnit", a, D(1));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Paren(a), b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.And, Paren(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Implies, Paren(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Iff, Paren(b));
    private static Formula Not(Formula a) =>
        Seq(Neg, Sp, Paren(a));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsF(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Paren(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Icc(Formula lo, Formula hi) => QCall("Finset", "Icc", lo, hi);
    private static Formula Product(Formula set, Formula body) =>
        QCall("Finset", "prod", set, Lambda("n", Nat(), body));
    private static Formula CastInt(Formula z) => QCall("Int", "cast", z);
    private static Formula Partition(Formula k) => QCall("Nat", "Partition", k);
    private static Formula Card(Formula p) => QCall("Fintype", "card", p);
    private static Formula Odd(Formula p) => Call("Odd", p);
    private static Formula ModEq(Formula modulus, Formula a, Formula b) =>
        QCall("Int", "ModEq", modulus, a, b);

    private static Formula IsGFBody()
    {
        Formula factor = Mul(
            Add(D(1), Mul(Pow(X(), N()), A())),
            Add(D(1), Mul(Pow(X(), Sub(N(), D(1))), Inverse(A()))));
        Formula product = Product(Icc(D(1), Add(M(), D(1))), factor);
        return And(Ne(Constant(A()), D(0)),
            All("m", Nat(), Eq(Coeff(M(), product), Coeff(M(), D(2)))));
    }

    private static Formula IsGFFormula() => Disp(All("A", PS(Rat()),
        Iff(Call("IsGF", A()), IsGFBody())));

    private static Formula OddPartition(Formula k) => Odd(Card(Partition(k)));

    private static Formula ParityWitness()
    {
        Formula witness = ExistsF("k", Nat(), And(Lt(D(0), K()),
            And(Eq(N(), Mul(D(2), K())), OddPartition(K()))));
        Formula zmodTwo = ModEq(D(4), Z(), D(2));
        return Imp(witness, zmodTwo);
    }

    private static Formula ZeroWitness()
    {
        Formula witness = ExistsF("k", Nat(), And(Lt(D(0), K()),
            And(Eq(N(), Mul(D(2), K())), OddPartition(K()))));
        return Imp(Not(witness), ModEq(D(4), Z(), D(0)));
    }

    private static Formula ClaimBody() => And(
        ExistsF("A", PS(Rat()), Call("IsGF", A())),
        All("A", PS(Rat()), Imp(Call("IsGF", A()), All("n", Nat(), Imp(
            Lt(D(0), N()), ExistsF("z", Int(), And(
                Eq(Coeff(N(), A()), CastInt(Z())),
                And(ParityWitness(), ZeroWitness()))))))));

    private static Formula ClaimFormula() => Disp(Iff(Call("claim"), ClaimBody()));
}
