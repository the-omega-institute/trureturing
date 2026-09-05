using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfResidueTransducerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A least-significant-first Fibonacci residue transducer computes canonical Zeckendorf values modulo every prime.",
        H("Zeckendorf Residue Transducer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-step-prefix-invariant"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/ZeckendorfResidueTransducer.residue_step_invariant"),
                H("Every finite prefix preserves the Fibonacci residue invariant"),
                StatementSource.FromAuthor(ResidueInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any prime p, least-significant-first bit word, Fibonacci index k, "
                        + "and starting residue r, the final residue is r plus the cast of the "
                        + "Fibonacci-weighted bit sum into ZMod p.")),
                    Paragraph(Text(
                        "The proof folds the state transition (r,u,v) to "
                        + "(r + b*u,v,u+v). Its private induction keeps u and v equal to the "
                        + "consecutive Fibonacci residues F_k and F_(k+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrary-bit-word-residue-correctness"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/ZeckendorfResidueTransducer.run_residue_eq_sum_fib_mod"),
                H("Every finite bit word evaluates to its Fibonacci sum modulo the prime"),
                StatementSource.FromAuthor(ArbitraryWordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The initial state is exactly (0,F_2,F_3), and the input word is read "
                        + "least-significant first. Taking the natural representative of the "
                        + "prefix invariant gives the ordinary remainder modulo p.")),
                    Paragraph(Text(
                        "This theorem applies to every finite Fin 2 word; it does not assume "
                        + "Zeckendorf admissibility or canonicality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-zeckendorf-residue-correctness"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/ZeckendorfResidueTransducer.zeckendorfResidueTransducer_correct"),
                H("Canonical Zeckendorf digits compute the original value modulo the prime"),
                StatementSource.FromAuthor(CanonicalWordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The repository's sparse descending wdigits list is expanded into a dense "
                        + "least-significant-first word beginning at Fibonacci index two.")),
                    Paragraph(Text(
                        "Canonicality proves that the dense word has the same Fibonacci-weighted "
                        + "sum as wdigits. The frozen decode_wdigits theorem is used only in the "
                        + "final rewrite from that sum to n."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Conventions/WDigits")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PrimeNaturals() => Call("Primes", Naturals());

    private static Formula BitWords() => Call("List", Call("Fin", D(2)));

    private static Formula Residues(Formula prime) => Call("ZMod", prime);

    private static Formula WeightedSum(Formula index, Formula bits) =>
        Call("fibonacciWeightedSumFrom", index, bits);

    private static Formula State(Formula residue, Formula first, Formula second) =>
        Seq(Open, residue, Comma, Sp, first, Comma, Sp, second, Close);

    private static Formula ResidueInvariantFormula()
    {
        Formula prime = F.Id("p");
        Formula bits = F.Id("bits");
        Formula index = F.Id("k");
        Formula residue = F.Id("r");
        Formula successorIndex = Seq(index, Sp, Plus, Sp, D(1));
        Formula start = State(
            residue,
            Call("fib", index),
            Call("fib", successorIndex));
        Formula run = Call("runResidueStateFrom", prime, start, bits);
        Formula cast = Call("cast", WeightedSum(index, bits), Residues(prime));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, prime, Sp, InMacro, Sp, PrimeNaturals(), Comma),
            Seq(Forall, Sp, bits, Sp, InMacro, Sp, BitWords(), Comma),
            Seq(Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Forall, Sp, residue, Sp, InMacro, Sp, Residues(prime), Comma),
            Seq(
                Call("residue", run), Sp, Eq, Sp,
                residue, Sp, Plus, Sp, cast, Dot),
        ]));
    }

    private static Formula ArbitraryWordFormula()
    {
        Formula prime = F.Id("p");
        Formula bits = F.Id("bits");

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, prime, Sp, InMacro, Sp, PrimeNaturals(), Comma),
            Seq(Forall, Sp, bits, Sp, InMacro, Sp, BitWords(), Comma),
            Seq(
                Call("runResidueBits", prime, bits), Sp, Eq, Sp,
                new Formula.Modulo(WeightedSum(D(2), bits), prime), Dot),
        ]));
    }

    private static Formula CanonicalWordFormula()
    {
        Formula prime = F.Id("p");
        Formula natural = F.Id("n");

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, prime, Sp, InMacro, Sp, PrimeNaturals(), Comma),
            Seq(Forall, Sp, natural, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                Call(
                    "runZeckendorfResidueTransducer",
                    prime,
                    Call("wdigits", natural)),
                Sp, Eq, Sp,
                new Formula.Modulo(natural, prime), Dot),
        ]));
    }
}
