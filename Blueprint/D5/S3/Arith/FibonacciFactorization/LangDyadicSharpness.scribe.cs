using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciFactorization;

internal sealed class LangDyadicSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciFactorization/LangDyadicSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact corrected common factors give a uniform counterexample to A319197 sharpness.",
        H("Correct Dyadic Factors and the A319197 Sharpness Counterexample"),
        Blocks(
            Paragraph(Text("Nat.fib denotes the original natural Fibonacci sequence. "
                + "The layer values and canonical divisors are integers. External level n "
                + "equals k+3, and the new layer index j corresponds to external entry a(j+4). "
                + "The corrected layers are A081459(j+2), an already published Newton-Pell sequence. "
                + "The result addresses the separately stated best-possible denominator claim; "
                + "it does not refute the power-of-two divisibility theorem.")),
            Describe.Lean(
                DescribeId.Create("lang-corrected-layer"),
                DeclarationHandle.Create(Prefix + "canonicalLayer"),
                H("Independently specified corrected layers"),
                StatementSource.FromAuthor(LayerFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Recurrence/lang2018a319197")),
                Blocks(Paragraph(Text("The integer sequence starts at nine and sends b to 2*b^2-1. "
                    + "This is A081459 with its first value two omitted. Its recurrence and Lucas "
                    + "interpretation are classical inputs, not a new sequence claim."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lang-corrected-divisor"),
                DeclarationHandle.Create(Prefix + "canonicalDivisor"),
                H("The corrected dyadic product"),
                StatementSource.FromAuthor(DivisorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k, multiply 2^(k+3) by the product of "
                    + "canonicalLayer j over j in Finset.range k. The empty product is one; "
                    + "canonicalDivisor 0 is eight. Its equality to an actual Fibonacci number "
                    + "and its exact common-divisor property are conclusions of result."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lang-seventh-sharpness-claim"),
                DeclarationHandle.Create(Prefix + "a319197SeventhSharpness"),
                H("The source sharpness assertion at level seven"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Recurrence/lang2018a319197")),
                Blocks(Paragraph(Text("The published offset is three. At level seven its listed "
                    + "denominator is 2^7*1*9*161*51841*6989569, and the Fibonacci index is 96*m. "
                    + "The claim says that no natural c greater than one makes c times this "
                    + "denominator divide every such Fibonacci number. Only the supplied prefix "
                    + "is used; no unspecified tail of the published sequence is invented."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lang-correction-and-sharpness-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("All-level exact factorization and a strict uniform enlargement"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural k, Nat.fib(6*2^k) equals the positive "
                        + "integer canonicalDivisor k. An integer d divides all Nat.fib(6*2^k*m), "
                        + "over every natural m including zero, exactly when d divides this "
                        + "canonical divisor. Thus it is the actual greatest positive common divisor.")),
                    Paragraph(Text("The proof simultaneously propagates the Fibonacci product "
                        + "and goldenLucas(6*2^k)=2*canonicalLayer k. It uses the existing Lucas "
                        + "doubling law and the original Fibonacci addition law. The even index "
                        + "makes the Lucas norm sign positive. The multiplier-one value provides "
                        + "necessity for maximality, and Fibonacci divisibility provides sufficiency.")),
                    Paragraph(Text("At k=4 the exact value is F_96=769*(2^7*1*9*161*51841*6989569). "
                        + "The same factor 769 works for every natural multiplier. Therefore "
                        + "a319197SeventhSharpness is false. Integrality of the published quotient "
                        + "at that level survives, but its value at multiplier one is 769. "
                        + "The conclusion makes no Wall-Sun-Sun existence claim."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nats() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula ExistsNat(string n, Formula body) => Seq(Exists, Sp, V(n), Sp, InMacro, Sp, Nats(), Comma, Sp, body);
    private static Formula C(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), xs);
    private static Formula Fib(Formula index) => new Formula.Apply(Seq(Operatorname, Grp(V("Nat"), Dot, V("fib"))), [index]);
    private static Formula FibZ(Formula index) => Par(Seq(Fib(index), Colon, Sp, Ints()));
    private static Formula Layer(Formula index) => C("canonicalLayer", index);
    private static Formula Divisor(Formula index) => C("canonicalDivisor", index);

    private static Formula LayerFormula() => Disp(And(Eqn(Layer(D(0)), D(9)),
        All("j", Nats(), Eqn(Layer(Add(V("j"), D(1))), Sub(Mul(D(2), Pow(Layer(V("j")), D(2))), D(1))))));
    private static Formula DivisorFormula() => Disp(All("k", Nats(), Eqn(Divisor(V("k")),
        Mul(Pow(D(2), Add(V("k"), D(3))), C("prod", C("range", V("k")), V("canonicalLayer"))))));
    private static Formula PublishedDenominator() =>
        Mul(Mul(Mul(Mul(Mul(Pow(D(2), D(7)), D(1)), D(9)), D(161)), D(51841)), D(6989569));
    private static Formula ClaimFormula() => Disp(Eqn(V("a319197SeventhSharpness"),
        C("Not", ExistsNat("c", And(Lt(D(1), V("c")), All("m", Nats(),
            Dvd(Mul(V("c"), PublishedDenominator()), Fib(Mul(D(96), V("m"))))))))));
    private static Formula ResultFormula()
    {
        var index = Mul(D(6), Pow(D(2), V("k")));
        var common = All("d", Ints(), Seq(
            Par(All("m", Nats(), Dvd(V("d"), FibZ(Mul(index, V("m")))))),
            Sp, Equiv, Sp, Par(Dvd(V("d"), Divisor(V("k"))))));
        var universal = All("k", Nats(), And(Eqn(FibZ(index), Divisor(V("k"))),
            And(Lt(D(0), Divisor(V("k"))), common)));
        return Disp(And(universal, C("Not", V("a319197SeventhSharpness"))));
    }
}
