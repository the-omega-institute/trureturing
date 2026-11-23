using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class WeightedLabelRecordDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact weighted readout optimum with a prescribed pure environment.",
        H("Weighted label records with a finite pure environment"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-label-record-optimum"),
            DeclarationHandle.Create(Prefix + "weightedLabelRecord_optimum"),
            H("Exact optimum and a product-cell realization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Observer/elroneldar2007optimalencoding"),
                LibraryNoteRef.Create("D5/L/Observer/frenkel2022classicalsimulations"),
                LibraryNoteRef.Create("D5/L/Entropy/clivaz2019unifying"),
                LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression"),
                LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance"),
                LibraryNoteRef.Create("D5/L/Divergence/jencovapetz2006sufficiency")),
            Blocks(
                Paragraph(Text(
                    "Let B be a finite input basis, J a nonempty finite label set, c a label map, "
                    + "and p a nonnegative prior of total mass one. The memory and pure environment "
                    + "have dimensions d and e, with e positive and the entire input basis fitting "
                    + "in d times e product cells. The score S is the prior-weighted trace pairing "
                    + "of the effect for c(b) with the environment-reduced column at each b.")),
                Paragraph(Text(
                    "For each label, sort the priors of that label in decreasing order and pad "
                    + "with zeros to length d times e. Sum each consecutive block of e entries. "
                    + "The value O is the sum of the d largest block masses across all labels. "
                    + "Every isometric encoder V and every positive semidefinite effect family E "
                    + "summing to the memory identity has score at most O.")),
                Paragraph(Text(
                    "For each label, rectangular characteristic polynomial commutation gives the "
                    + "spectrum of the encoded prior diagonal with zero padding. Tensoring an effect "
                    + "with the environment identity repeats each of its eigenvalues e times. "
                    + "Von Neumann's trace inequality bounds each label's score by the scalar "
                    + "product of its block masses and decreasing effect eigenvalues. The effect "
                    + "eigenvalues lie in the unit interval and sum to d across the POVM.")),
                Paragraph(Text(
                    "Assign the chosen blocks distinct memory rows, and pack each selected input "
                    + "into the environment coordinate of its block. Extend this injection to all "
                    + "basis vectors, including those with prior zero. The encoder Vg has the "
                    + "single unit entry at g(b) in column b. The effect Er(j) is the diagonal "
                    + "projector onto rows whose readout label r is j. These effects are positive "
                    + "semidefinite, sum to the identity, square to themselves, and have zero "
                    + "pairwise products for distinct labels.")),
                Paragraph(Text(
                    "The endpoint uses the existing perfect label record criterion on the "
                    + "positive-prior support. The slot cost is the sum of the class sizes "
                    + "on that support divided by e and rounded up separately for each label.")),
                Paragraph(Text(
                    "Elron and Eldar Theorem 2 optimizes independently selectable code states. "
                    + "Frenkel Theorem 2.4 supplies the classical simulation under separate "
                    + "spectral constraints. Clivaz et al. Appendix Lemma 4 and Eq. (43) give "
                    + "the environment-sized spectral blocks. The attaining construction here "
                    + "packs the chosen blocks into one isometry on the original basis. Kato, "
                    + "Koashi and Imoto, and Jencova and Petz provide the exact compression and "
                    + "sufficiency context of the perfect-readout criterion."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-optimal-success"),
                DeclarationHandle.Create(Prefix + "uniform_optimalSuccess_eq"),
                H("Exact uniform success from full blocks and remainders"),
                StatementSource.FromAuthor(UniformFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Observer/elroneldar2007optimalencoding"),
                    LibraryNoteRef.Create("D5/L/Observer/nomurahan2012secondorder")),
                Blocks(
                    Paragraph(Text(
                        "Let B be a nonempty finite input basis and J a finite set of labels, "
                        + "with c from B to J. Write N for the basis cardinality and m_j for the "
                        + "size of the fibre over j, which may be zero. The prior u assigns 1/N "
                        + "to every basis word. Take positive e and N at most d times e. "
                        + "The optimum O is the same common-isometry, arbitrary-POVM optimum above.")),
                    Paragraph(Text(
                        "Write K for the sum of the integer quotients m_j divided by e. R(c,e,k) "
                        + "sums the largest k residues m_j modulo e, padding with zeros. "
                        + "The positive uniform weights form a prefix of each sorted padded list. "
                        + "Every full block strictly outweighs each remainder and K is at most d. "
                        + "After the full blocks, at most one positive block from each class competes "
                        + "for the remaining slots.")),
                    Paragraph(Text(
                        "The weighted block theorem above supplies the operational optimum. "
                        + "Elron and Eldar Theorem 2 treats separately prepared code states. "
                        + "Nomura and Han Section VII gives classical fixed-length information-spectrum "
                        + "bounds. Publication priority for the combination of full-input isometry, "
                        + "fixed environment, and classwise remainder allocation is open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-record-memory-bounds"),
                DeclarationHandle.Create(Prefix + "uniform_record_memory_bounds"),
                H("Necessary and sufficient memory bounds from a minimum class cover"),
                StatementSource.FromAuthor(MemoryFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Observer/nomurahan2012secondorder")),
                Blocks(
                    Paragraph(Text(
                        "Use the same finite model and feasibility assumptions. Class mass is "
                        + "the sum of the fibre sizes divided by N. Suppose M is the least cardinality "
                        + "of a label set with class mass at least alpha. Put C equal to the ceiling "
                        + "of N/e and J_full equal to the number of fibres of size at least e. "
                        + "Reaches(alpha,d,e,c) means there exist a full-input isometric encoder "
                        + "and a memory POVM with average success at least alpha under u.")),
                    Paragraph(Text(
                        "The K full blocks represent J_full classes and the remaining d minus K "
                        + "slots can represent at most that many additional classes. Conversely, "
                        + "a minimum cover fits using at most K full blocks and M remainder blocks. "
                        + "For alpha strictly between zero and one, the least feasible d reaching "
                        + "alpha therefore lies between the two displayed dimensions."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);

    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), args);

    private static Formula UniformFormula()
    {
        Formula c = F.Id("c"), d = F.Id("d"), e = F.Id("e"), n = F.Id("N");
        Formula k = Call("K", c, e);
        return Disp(new Formula.Aligned([
            UniformHypotheses(),
            Seq(n, Sp, Cdot, Sp, Call("O", c, F.Id("u"), d, e), Sp, Eq, Sp,
                e, Sp, Cdot, Sp, k, Sp, Plus, Sp, Call("R", c, e, Seq(d, Sp, Minus, Sp, k))),
        ]));
    }

    private static Formula MemoryFormula()
    {
        Formula c = F.Id("c"), d = F.Id("d"), e = F.Id("e"), n = F.Id("N");
        Formula a = Alpha, m = F.Id("M"), k = Call("K", c, e);
        Formula ceil = Call("ceil", Seq(n, Slash, e));
        Formula full = Call("FullLabels", c, e), reaches = Call("Reaches", a, d, e, c);
        return Disp(new Formula.Aligned([
            UniformHypotheses(),
            Seq(Call("MinimumCover", c, a, m), Sp, Rightarrow),
            Seq(Open, reaches, Sp, Rightarrow, Sp,
                Apply(Max, ceil, Seq(k, Sp, Plus, Sp, m, Sp, Minus, Sp, full)), Sp, Leq, Sp, d, Close),
            Seq(Land, Sp, Open, Apply(Max, ceil, Seq(k, Sp, Plus, Sp, m)), Sp, Leq, Sp, d,
                Sp, Rightarrow, Sp, reaches, Close),
        ]));
    }

    private static Formula UniformHypotheses()
    {
        Formula b = F.Id("B"), j = F.Id("J"), c = F.Id("c");
        Formula d = F.Id("d"), e = F.Id("e"), n = F.Id("N");
        return Seq(Call("FiniteTypes", b, j), Sp, Land, Sp, Call("Nonempty", b), Sp, Land, Sp,
            c, Sp, InMacro, Sp, Call("Map", b, j), Sp, Land, Sp, D(0), Sp, Lt, Sp, e, Sp, Land, Sp,
            n, Sp, Leq, Sp, d, Sp, Cdot, Sp, e, Sp, Rightarrow);
    }

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("B"), j = F.Id("J"), d = F.Id("d"), e = F.Id("e"), p = F.Id("p");
        Formula c = F.Id("c"), v = F.Id("V"), f = F.Id("E"), g = F.Id("g"), r = F.Id("r");
        Formula opt = Call("O", c, p, d, e);
        Formula cells = Seq(Call("Fin", d), Sp, Times, Sp, Call("Fin", e));
        Formula vg = Seq(F.Id("V"), Underscore, Grp(g));
        Formula er = Seq(F.Id("E"), Underscore, Grp(r));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, b, Comma, j, Sp, InMacro, Sp, Seq(Operatorname, Grp(F.Id("FiniteTypes"))), Comma,
                d, Comma, e, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                c, Sp, InMacro, Sp, Call("Map", b, j), Comma,
                p, Sp, InMacro, Sp, Call("Map", b, Seq(Mathbb, Grp(F.Id("R")))), Comma),
            Seq(Call("Nonempty", j), Sp, Land, Sp, D(0), Sp, Lt, Sp, e, Sp, Land, Sp,
                Call("card", b), Sp, Leq, Sp, d, Sp, Cdot, Sp, e, Sp, Land, Sp,
                Call("prior", p), Sp, Rightarrow),
            Seq(Open, Forall, Sp, v, Sp, InMacro, Sp, Call("EncoderMatrices", b, cells), Comma,
                f, Sp, InMacro, Sp, Call("EffectFamilies", j, Call("Fin", d)), Comma,
                Call("isometry", v), Sp, Land, Sp,
                Call("POVM", f, j), Sp, Rightarrow, Sp, Call("S", c, p, v, f), Sp, Leq, Sp, opt, Close,
                Sp, Land),
            Seq(Open, Exists, Sp, g, Sp, InMacro, Sp, Call("Embedding", b, cells), Comma,
                r, Sp, InMacro, Sp, Call("Map", Call("Fin", d), j), Comma,
                Call("isometry", vg), Sp, Land, Sp, Call("PVM", er, j), Sp, Land, Sp,
                Call("S", c, p, vg, er), Sp, Eq, Sp, opt, Close, Sp, Land),
            Seq(Open, opt, Sp, Eq, Sp, D(1), Sp, Iff, Sp, Call("memorySlots", c, p, e),
                Sp, Leq, Sp, d, Close),
        ]));
    }
}
