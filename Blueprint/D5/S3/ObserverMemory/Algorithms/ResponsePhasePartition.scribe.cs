using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ResponsePhasePartitionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded monotone ranks construct maximal native phases and one coherent final phase.",
        H("Native Response Phase Partitions"),
        Blocks(
            Paragraph(Text(
                "The coordinate type A is finite and may be empty. Replies have arbitrary "
                + "universe and need no order. An explicit injective map into Fin(q+1) "
                + "reflects equality; each installed coordinate is monotone in this rank. "
                + "Write Adj(b) for IsChain of b with relation left.snd unequal to right.snd, "
                + "and CoordinateMonotone(rank,obs) for monotonicity of the ranked reply "
                + "at every coordinate, over all natural epochs.")),
            Describe.Lean(DescribeId.Create("potential"), Handle("potential"),
                H("Potential of the entire installed field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For finite A, arbitrary R, natural q, rank from R to Fin(q+1), "
                    + "observation field obs from natural epochs to A to R, and epoch j, "
                    + "potential(rank,obs,j) is the sum over all a in A of rank(obs(j,a)).val. "
                    + "It lies between zero and q times card A. Coordinate monotonicity "
                    + "makes this sum nondecreasing. On two comparable epochs, a changed "
                    + "response vector has a changed coordinate; injectivity and the finite "
                    + "sum strict comparison charge at least one unit to that change."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-response-partition"),
                Handle("finite_response_partition"), H("Finite native phases with sharp charge"),
                StatementSource.FromAuthor(FiniteFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every N at most J, the original native Partition covers [N,J+1) "
                        + "with nonempty intervals, strictly increasing delimiters and exact "
                        + "terminal delimiter J+1. Adjacent replies differ, so these are "
                        + "maximal constant-response intervals within [N,J]. The sharper "
                        + "bound is length plus potential at N at most potential at J plus one. "
                        + "It implies at most q times card A plus one phases. No change is "
                        + "required after J.")),
                    Paragraph(Text(
                        "Construct the partition by backward interval-length induction. "
                        + "A singleton epoch has its observation as reply. For the suffix "
                        + "starting at N+1, its first nonempty guard identifies its reply "
                        + "with obs(N+1). If obs(N) agrees, extend that guard to N. Otherwise "
                        + "prepend the singleton epoch and charge its extra block to the "
                        + "strict potential increase. The guard and delimiter invariants "
                        + "are carried by this same construction.")),
                    Paragraph(Text(
                        "When A is empty or q is zero the count is one. N equals J gives "
                        + "the one-epoch partition. Duplicate installed addresses and "
                        + "simultaneous coordinate changes do not add separate phases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-line-response-partition"),
                Handle("half_line_response_partition"), H("One prefix for every cutoff"),
                StatementSource.FromAuthor(HalfLineFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each N choose one finite prefix b, start s and reply z before "
                        + "quantifying over cutoffs. The field equals z at every epoch from s. "
                        + "The prefix followed by z has distinct adjacent replies and at most "
                        + "q times card A plus one blocks. Every J at least s has exactly the "
                        + "native partition b appended with [(J+1,z)]. Thus all cutoffs share "
                        + "the same prefix and final guard; an empty prefix starts that guard "
                        + "at N.")),
                    Paragraph(Text(
                        "Apply the finite-order monotone-chain condition to the entire rank "
                        + "vector. Rank injectivity reflects its stabilized equality to the "
                        + "observation field. Take a stable epoch T at least N and the finite "
                        + "native partition through T. Split off its last block and retain "
                        + "that block's actual start s. Its old finite guard and the stable "
                        + "tail prove constancy from s. Replacing only the last delimiter "
                        + "works also when s is at most J and J is less than T. Appending an "
                        + "extra equal-response tail would lose maximality.")),
                    Paragraph(Text(
                        "This is an existential coherent phase decomposition. It supplies "
                        + "no computable last-change detector or bound on s, phase duration, "
                        + "reads, instructions or updates. Changes can be arbitrarily delayed."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the uniform descriptor task, A is ALL installed read-state occurrences "
                + "E_R, including unvisited states and occurrences installing duplicate "
                + "literals. Fix one common descriptor tuple and one original source u. "
                + "At coordinate e, obs(j,e) is the read of its fixed installed literal "
                + "p(delta_e) on U iterated j times applied to u. Every phase uses this same "
                + "source and tuple. In the native program Q=E, a read state e reads that "
                + "occurrence's installed literal. The vector in the proof adds no "
                + "simultaneous-response access port.")),
            Paragraph(Text(
                "UDB.5 gives rank monotonicity after reach. Reach persistence and the "
                + "least absent rank supply the remaining comparable epochs, yielding "
                + "UDB.6 coordinate by coordinate. The injective rank hypothesis remains "
                + "explicit. The source says finite ordered alphabet without explicitly "
                + "saying linear; StrictMono.injective requires a LinearOrder domain. "
                + "An order interpretation establishing equality reflection is therefore "
                + "a separate source condition. No unconditional theorem for arbitrary "
                + "partial reply orders follows.")),
            Paragraph(Text(
                "The native guards can be combined with guarded_phase_execution for the "
                + "same program and observation field. Effective shared-source guard "
                + "formulas, rank and descriptor synthesis, and their full uniform "
                + "composition remain separate obligations. This component is a "
                + "repository-derived construction using the pinned finite-sum and "
                + "monotone-chain results; no literature novelty is asserted.")))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => Seq(args.SelectMany((arg, i) =>
        i == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray());
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PlusOne(Formula x) => Seq(x, Sp, Plus, Sp, D(1));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula Last(Formula b, Formula j, Formula z) =>
        Seq(b, Sp, Plus, Plus, Sp, OpenBracket, Pair(PlusOne(j), z), CloseBracket);
    private static Formula Telescope(Formula body, bool finite)
    {
        Formula a = F.Id("A"), r = F.Id("R"), q = F.Id("q"), f = F.Id("f"),
            k = F.Id("k"), n = F.Id("N"), j = F.Id("J");
        return Disp(Seq(Forall, Sp, a, Comma, Sp, r, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("Fintype", a), CloseBracket, Comma, Sp,
            Forall, Sp, q, InMacro, Sp, Nat, Comma, Esc,
            Forall, Sp, f, Colon, Sp, Nat, Sp, To, Sp, a, Sp, To, Sp, r, Comma, Sp,
            k, Colon, Sp, r, Sp, To, Sp, Call("Fin", PlusOne(q)), Comma, Esc,
            Call("Injective", k), Sp, Land, Sp, Call("CoordinateMonotone", k, f),
            Sp, Implies, Esc,
            Forall, Sp, n, InMacro, Sp, Nat, Comma, Sp,
            finite ? Seq(Forall, Sp, j, InMacro, Sp, Nat, Comma, Sp,
                n, Sp, Leq, Sp, j, Sp, Implies, Esc) : Sp,
            body));
    }
    private static Formula FiniteFormula()
    {
        Formula b = F.Id("b"), a = F.Id("A"), r = F.Id("R"),
            f = F.Id("f"), k = F.Id("k"), n = F.Id("N"), j = F.Id("J");
        return Telescope(Seq(Exists, Sp, b, Colon, Sp,
            Call("List", Seq(Nat, Sp, Times, Sp, Open, a, Sp, To, Sp, r, Close)), Comma, Esc,
            Call("Partition", f, n, PlusOne(j), b), Sp, Land, Sp, Call("Adj", b), Sp, Land, Esc,
            Call("length", b), Sp, Plus, Sp, Call("potential", k, f, n), Sp, Leq, Sp,
            PlusOne(Call("potential", k, f, j))), true);
    }
    private static Formula HalfLineFormula()
    {
        Formula b = F.Id("b"), a = F.Id("A"), r = F.Id("R"),
            q = F.Id("q"), f = F.Id("f"), n = F.Id("N"), j = F.Id("J"),
            s = F.Id("s"), z = F.Id("z");
        return Telescope(Seq(Exists, Sp, b, Colon, Sp,
            Call("List", Seq(Nat, Sp, Times, Sp, Open, a, Sp, To, Sp, r, Close)), Comma, Sp,
            s, InMacro, Sp, Nat, Comma, Sp, z, Colon, Sp, a, Sp, To, Sp, r, Comma, Esc,
            n, Sp, Leq, Sp, s, Sp, Land, Sp,
            Open, Forall, Sp, j, InMacro, Sp, Nat, Comma, Sp, s, Sp, Leq, Sp, j,
            Sp, Implies, Sp, Seq(f, Open, j, Close), Sp, Eq, Sp, z, Close, Sp, Land, Esc,
            Call("Adj", Last(b, s, z)), Sp, Land, Sp,
            PlusOne(Call("length", b)), Sp, Leq, Sp,
            PlusOne(Seq(q, Sp, Times, Sp, Call("card", a))), Sp, Land, Esc,
            Forall, Sp, j, InMacro, Sp, Nat, Comma, Sp, s, Sp, Leq, Sp, j,
            Sp, Implies, Sp, Call("Partition", f, n, PlusOne(j), Last(b, j, z))), false);
    }
}
