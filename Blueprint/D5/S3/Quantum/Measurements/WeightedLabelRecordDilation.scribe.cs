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
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);

    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), args);

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
