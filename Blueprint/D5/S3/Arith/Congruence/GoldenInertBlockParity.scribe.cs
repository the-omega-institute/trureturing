using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class GoldenInertBlockParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/GoldenInertBlockParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed mod-five character is an exact parity readout of prime multiplicities, "
            + "and every odd-inert-base Fibonacci power layer has a negative readout.",
        H("Golden Inert Factors and Power-Layer Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-inert-chi"),
                DeclarationHandle.Create(Prefix + "chi"),
                H("Fixed quadratic character"),
                StatementSource.FromAuthor(ChiFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, chi n is the integer-valued Legendre symbol legendreSym 5 (n : Int). The first argument is the modulus five. For odd primes other than five, quadratic reciprocity identifies it with the split or inert sign in the fixed field Q(sqrt(5))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-inert-oddInertFactors"),
                DeclarationHandle.Create(Prefix + "oddInertFactors"),
                H("Odd-multiplicity inert prime divisors"),
                StatementSource.FromAuthor(FactorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N, retain from N.primeFactors exactly the primes p with chi p=-1 and Odd (N.factorization p). This counts distinct prime values, using their actual multiplicities in N. It is not the radical and not a count of all inert prime divisors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-inert-powerBlock"),
                DeclarationHandle.Create(Prefix + "powerBlock"),
                H("Consecutive Fibonacci power-index quotient"),
                StatementSource.FromAuthor(BlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural ell and k, powerBlock ell k is Nat.fib (ell^(k+1)) / Nat.fib (ell^k), with natural division. The later odd-inert hypotheses guarantee that the denominator is positive, and Fibonacci divisibility proves exact division. The initial layer k=0 is F_ell/F_1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-inert-character-eq-odd-inert-sign"),
                DeclarationHandle.Create(Prefix + "character_eq_odd_inert_sign"),
                H("Character is the parity of odd-depth inert support"),
                StatementSource.FromAuthor(CharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero natural N not divisible by five, chi N equals (-1) raised to the cardinality of oddInertFactors N. The proof applies the actual Legendre homomorphism to the actual prime factorization, then counts negative factors whose exponents are odd. Arbitrary exponents are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-odd-inert-count-iff"),
                DeclarationHandle.Create(Prefix + "odd_inert_count_iff"),
                H("Exact negative-character equivalence"),
                StatementSource.FromAuthor(CountIffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero natural N not divisible by five, oddInertFactors N has odd cardinality if and only if chi N=-1. The finite set may have more than one member. This theorem does not force any exponent to be one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-fibonacci-mod-five"),
                DeclarationHandle.Create(Prefix + "fibonacci_mod_five"),
                H("The ramified recurrence for every index"),
                StatementSource.FromAuthor(ModFiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, F_(n+1) equals (n+1)*3^n in ZMod 5. The proof uses the two-step Fibonacci recurrence at arbitrary n, including both base indices. This is a universal equality, not a finite residue table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-odd-index-character"),
                DeclarationHandle.Create(Prefix + "odd_index_character"),
                H("Odd Fibonacci index preserves character"),
                StatementSource.FromAuthor(OddIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd natural n, chi (Nat.fib n)=chi n. The result also allows multiples of five, where both characters are zero. The extra factor 3^(n-1) in the mod-five formula is a square when n is odd."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-power-block-character"),
                DeclarationHandle.Create(Prefix + "power_block_character"),
                H("Every odd-inert power layer has negative character"),
                StatementSource.FromAuthor(PowerCharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural ell and k with Odd ell and chi ell=-1, the actual powerBlock ell k has character -1. Primality of ell is not required for this character identity. Exact-rank and initial-WSS-depth conclusions for prime bases are additional ordinary results in the WSS problem dossier, not conclusions of this Lean declaration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-power-block-odd-inert-count"),
                DeclarationHandle.Create(Prefix + "power_block_odd_inert_count"),
                H("Odd inert support in each actual layer"),
                StatementSource.FromAuthor(PowerCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same odd-inert-base hypotheses, the number of distinct prime divisors with negative character and odd exponent in the exact Fibonacci quotient is odd. It is the local layer count, even when the cumulative power index is a square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-power-block-inert-witness"),
                DeclarationHandle.Create(Prefix + "power_block_inert_witness"),
                H("An actual prime divisor with odd exponent"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd inert natural base ell and every natural k, there exists a natural prime p dividing powerBlock ell k with chi p=-1 and odd actual factorization exponent. The declaration does not identify this exponent with initial WSS depth for composite bases. The separate ordinary prime-base argument proves that identification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-inert-inertMultiplicationSystem"),
                DeclarationHandle.Create(Prefix + "inertMultiplicationSystem"),
                H("The existing involutive readout carrier"),
                StatementSource.FromAuthor(SystemFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural p with chi p=-1, instantiate the existing InvolutiveReadoutSystem with State=Nat and Readout=Int. Its step is M |-> p*M, its readout is chi, and its flip is integer negation. Multiplicativity proves readout_step and neg_neg proves involutivity. No statement about the original integer state returning is built into the carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-inert-inert-power-readout"),
                DeclarationHandle.Create(Prefix + "inert_power_readout"),
                H("Literal arithmetic specialization of odd and even readouts"),
                StatementSource.FromAuthor(ReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural p,M,k with chi p=-1, even k implies chi(p^k*M)=chi M, and odd k implies chi(p^k*M)=-chi M. The proof invokes the existing even_iterate_completes_readout and odd_iterate_flips_readout on inertMultiplicationSystem, and proves that its actual k-step integer state is p^k*M. These parity statements concern the character only."))),
                DescribeRole.Theorem))));

    private static Formula V(string n) => F.Id(n);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var terms = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; ++i)
        {
            if (i > 0) { terms.Add(Comma); terms.Add(Sp); }
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return Seq([.. terms]);
    }
    private static Formula AllN(string n, Formula body) =>
        Seq(Forall, Sp, V(n), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula ExN(string n, Formula body) =>
        Seq(Exists, Sp, V(n), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("mul", a, b);
    private static Formula Fib(Formula a) => Call("Nat.fib", a);
    private static Formula Chi(Formula a) => Call("chi", a);
    private static Formula Factors(Formula a) => Call("oddInertFactors", a);
    private static Formula Count(Formula a) => Call("card", Factors(a));
    private static Formula Block() => Call("powerBlock", V("ell"), V("k"));
    private static Formula MinusOne() => Call("neg", V("1"));
    private static Formula Domain() => Call("And", Call("Not", Eqn(V("N"), V("0"))),
        Call("Not", Call("Divides", V("5"), V("N"))));
    private static Formula InertBase() => Call("And", Call("Odd", V("ell")),
        Eqn(Chi(V("ell")), MinusOne()));
    private static Formula Layer(Formula body) => Disp(AllN("ell", AllN("k",
        Call("Implies", InertBase(), body))));

    private static Formula ChiFormula() => Disp(AllN("n", Eqn(Chi(V("n")),
        Call("legendreSym", V("5"), Call("Int.cast", V("n"))))));
    private static Formula FactorsFormula()
    {
        var keep = Call("And", Eqn(Chi(V("p")), MinusOne()),
            Call("Odd", Call("Nat.factorization", V("N"), V("p"))));
        return Disp(AllN("N", Eqn(Factors(V("N")), Call("filter",
            Call("lambda", V("p"), keep), Call("Nat.primeFactors", V("N"))))));
    }
    private static Formula BlockFormula() => Disp(AllN("ell", AllN("k", Eqn(Block(),
        Call("Nat.div", Fib(Pow(V("ell"), Add(V("k"), V("1")))),
            Fib(Pow(V("ell"), V("k"))))))));
    private static Formula CharacterFormula() => Disp(AllN("N", Call("Implies", Domain(),
        Eqn(Chi(V("N")), Pow(MinusOne(), Count(V("N")))))));
    private static Formula CountIffFormula() => Disp(AllN("N", Call("Implies", Domain(),
        Call("Iff", Call("Odd", Count(V("N"))), Eqn(Chi(V("N")), MinusOne())))));
    private static Formula ModFiveFormula()
    {
        var index = Add(V("n"), V("1"));
        var left = Call("castToZMod", V("5"), Fib(index));
        var right = Mul(Call("castToZMod", V("5"), index),
            Pow(Call("castToZMod", V("5"), V("3")), V("n")));
        return Disp(AllN("n", Eqn(left, right)));
    }
    private static Formula OddIndexFormula() => Disp(AllN("n", Call("Implies", Call("Odd", V("n")),
        Eqn(Chi(Fib(V("n"))), Chi(V("n"))))));
    private static Formula PowerCharacterFormula() => Layer(Eqn(Chi(Block()), MinusOne()));
    private static Formula PowerCountFormula() => Layer(Call("Odd", Count(Block())));
    private static Formula WitnessFormula()
    {
        var body = Call("And", Call("Nat.Prime", V("p")),
            Call("Divides", V("p"), Block()), Eqn(Chi(V("p")), MinusOne()),
            Call("Odd", Call("Nat.factorization", Block(), V("p"))));
        return Layer(ExN("p", body));
    }

    private static Formula SystemFormula()
    {
        var sys = Call("inertMultiplicationSystem", V("p"));
        var data = Call("And", Eqn(Call("step", sys, V("M")), Mul(V("p"), V("M"))),
            Eqn(Call("readout", sys, V("M")), Chi(V("M"))),
            Eqn(Call("flip", sys, V("z")), Call("neg", V("z"))));
        var overIntegers = Seq(Forall, Sp, V("z"), Sp, InMacro, Sp,
            Seq(Mathbb, Grp(V("Z"))), Comma, Sp, data);
        return Disp(AllN("p", Call("Implies", Eqn(Chi(V("p")), MinusOne()),
            AllN("M", overIntegers))));
    }
    private static Formula ReadoutFormula()
    {
        var value = Chi(Mul(Pow(V("p"), V("k")), V("M")));
        var clauses = Call("And",
            Call("Implies", Call("Even", V("k")), Eqn(value, Chi(V("M")))),
            Call("Implies", Call("Odd", V("k")), Eqn(value, Call("neg", Chi(V("M"))))));
        return Disp(AllN("p", AllN("M", AllN("k",
            Call("Implies", Eqn(Chi(V("p")), MinusOne()), clauses)))));
    }
}
