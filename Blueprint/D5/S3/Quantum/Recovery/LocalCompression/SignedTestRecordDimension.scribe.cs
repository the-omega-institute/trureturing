using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class SignedTestRecordDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension";
    private static readonly LibraryNoteRef Kuroiwa =
        LibraryNoteRef.Create("D5/L/HilbertOperators/kuroiwa2021signleakage");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A static reconstruction-error obstruction for a finite experiment with a bounded encoder environment.",
        H("Signed tests and record dimension"),
        Blocks(
            Definition("sign-leakage", "signLeakage", "Sign leakage",
                "For a Hermitian test H and its strictly positive spectral projection P, "
                + "the form L on a square matrix X sums the real traces of "
                + "(I − P) X H⁺ X† and P X H⁻ X†. H⁺ and H⁻ are the positive and negative "
                + "parts of H, respectively. These pairings give the squared Frobenius "
                + "leakages with the full spectral weights."),
            Describe.Lean(
                DescribeId.Create("sum-sign-leakage"),
                DeclarationHandle.Create(Module + ".sum_signLeakage_eq"),
                H("Exact Kraus sign leakage"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kuroiwa),
                Blocks(Paragraph(Text(
                    "For a finite trace-preserving square Kraus map T with matrices Kₐ "
                    + "and a Hermitian test H, the sum of L(Kₐ) is the real trace of "
                    + "P(H − T(H)). The identity holds for singular tests and follows "
                    + "by applying trace preservation to H⁺. Kuroiwa's Chapter 4, "
                    + "Lemma 4.6, equations (4.23)–(4.24), supplies the sign-leakage terms."))),
                DescribeRole.Theorem),
            Definition("label-projection", "labelProjection", "Auxiliary label projections",
                "For a label map g on a finite basis, Qⱼ is diagonal with entry one at b "
                + "when g(b) = j and zero otherwise."),
            Definition("label-density", "labelDensity", "Auxiliary label densities",
                "With coordinate masses m(b), the diagonal matrix Ωⱼ has entry m(b) on "
                + "coordinates b of label j and zero on the others."),
            Definition("label-leakage", "labelLeakage", "Density-weighted label loss",
                "The form F on X is the sum over j of the real trace of "
                + "(I − Qⱼ)XΩⱼX†."),
            Definition("encoder-slice", "encoderSlice", "Encoder environment slices",
                "For V mapping the input basis into memory times environment, the slice Aₜ "
                + "has entry V((a,t),b) at memory row a and input column b."),
            Definition("record-kraus", "recordKraus", "Composite Kraus matrices",
                "For a CPTP decoder D and encoder slices Aₜ, the composite Kraus family "
                + "has entries BₛAₜ for the canonical Kraus family Bₛ of D."),
            Definition("decoder-effect", "decoderEffect", "Induced memory effects",
                "The memory effect Mⱼ is the trace adjoint of the decoder applied to Qⱼ."),
            Describe.Lean(
                DescribeId.Create("label-deficit"),
                DeclarationHandle.Create(Module + ".label_deficit_eq"),
                H("Actual label loss and the memory score"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty finite label set of cardinality r whose coordinate "
                    + "masses sum to one within each label, let V be an isometry on the "
                    + "whole input basis and D a CPTP decoder. Then the sum of F(BₛAₜ) "
                    + "over both Kraus indices equals r times one minus the average success "
                    + "of the effects Mⱼ on the environment-reduced columns of V, with "
                    + "coordinate prior p(b) = m(b)/r. Trace preservation gives the total "
                    + "input weight and the Kraus trace-adjoint pairing gives the success."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("label-count-memory-bound"),
                DeclarationHandle.Create(Module + ".label_count_sub_memory_le_deficit"),
                H("Label count and memory dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative coordinate masses of total one per label, the loss "
                    + "of a full-input isometry and common CPTP decoder is at least r − d. "
                    + "Each encoded auxiliary density is at most the identity, so the sum "
                    + "of the correct-label pairings is at most the sum of the decoder "
                    + "effect traces, which is d by POVM completeness. With the same "
                    + "signed tests and quadratic dominance, r − d is bounded by the "
                    + "same reconstruction-error budget."))),
                DescribeRole.Theorem),
            Definition("preparation", "preparation", "Preparation matrices",
                "The plain complex matrix underlying an input density state."),
            Definition("signed-test", "signedTest", "Finite signed tests",
                "A sum of the preparation matrices with the specified real coefficients."),
            Definition("signed-test-leakage", "signedTestLeakage", "Sign loss of a signed test",
                "The full Jordan-part leakage form of the Hermitian test with the specified coefficients."),
            Describe.Lean(
                DescribeId.Create("signed-test-record-dimension"),
                DeclarationHandle.Create(Module + ".signed_test_record_dimension"),
                H("Weighted signed-test dimension obstruction"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(
                    Kuroiwa,
                    LibraryNoteRef.Create("D5/L/Observer/elroneldar2007optimalencoding"),
                    LibraryNoteRef.Create("D5/L/Observer/frenkel2022classicalsimulations"),
                    LibraryNoteRef.Create("D5/L/Entropy/clivaz2019unifying"),
                    LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression")),
                Blocks(
                    Paragraph(Text(
                        "Let B be the whole finite input basis, and let the auxiliary labels "
                        + "form a nonempty finite set of size r. Each coordinate has a label g(b) "
                        + "and a nonnegative mass m(b), with mass one per label. The basis "
                        + "includes the zero-mass coordinates. Let V be an isometry from this "
                        + "basis into memory of dimension d and a pure environment of dimension "
                        + "e > 0, so |B| ≤ de. Let D be one CPTP decoder from memory to input.")),
                    Paragraph(Text(
                        "For a finite family of input states ρᵢ and finitely many real signed "
                        + "coefficient rows cₗ, form Hₗ = ∑ᵢ cₗᵢρᵢ. The bound assumes "
                        + "wₗ ≥ 0 and F(X) ≤ ∑ₗ wₗ Lₗ(X) for every square complex matrix X. "
                        + "Here Lₗ is the full sign-leakage form for Hₗ. The parameter δ bounds "
                        + "each full trace-norm error after applying V, discarding its "
                        + "environment and applying D.")),
                    Paragraph(Text(
                        "O(g,p,d,e) is the exact weighted label optimum with p(b) = m(b)/r. "
                        + "It sums the d largest masses among consecutive e-entry blocks of "
                        + "the separately sorted and zero-padded prior lists of the labels. "
                        + "The decoder effects form a POVM and the actual score is at most O "
                        + "by WeightedLabelRecordDilation.weightedLabelRecord_optimum. Its "
                        + "spectral packing uses the sources documented with that theorem. "
                        + "Applying the quadratic dominance to each composite Kraus operator "
                        + "and the trace-zero effect bound to each test gives the displayed error "
                        + "budget, using the finite signed-sum trace-norm triangle inequality.")),
                    Paragraph(Text(
                        "Kato §VII motivates the approximate local-compression question. "
                        + "The estimate concerns the full trace-norm errors of a fixed finite "
                        + "experiment under one encoder and decoder in one use, with the pure "
                        + "environment bound imposed on the encoder."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string name, string heading, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula Bound()
    {
        Formula g = F.Id("g"), p = F.Id("p"), d = F.Id("d"), e = F.Id("e");
        Formula r = F.Id("r"), l = F.Id("l"), i = F.Id("i"), c = F.Id("c"), w = F.Id("w");
        Formula opt = new Formula.Apply(F.Id("O"), [g, p, d, e]);
        return Disp(Seq(r, Sp, Open, D(1), Sp, Minus, Sp, opt, Close, Sp, Leq, Sp, DeltaLower, Sp,
            Sum, Underscore, Grp(l), Sp, w, Underscore, Grp(l), Sp,
            Frac, Grp(Seq(Sum, Underscore, Grp(i), Sp, Lvert, Sp, c, Underscore,
                Grp(Seq(l, i)), Sp, Rvert)), Grp(D(2))));
    }
}
