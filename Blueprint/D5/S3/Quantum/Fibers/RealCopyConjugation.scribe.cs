using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class RealCopyConjugationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Fibers/RealCopyConjugation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complete real joint measurement on at least two independent copies determines "
            + "a complex density state up to conjugation in the specified real basis.",
        H("Real Copy Statistics and Conjugation"),
        Blocks(
            Entry("matrix", "stateMatrix", "Native density-state matrix coordinates",
                "The input is the native density-state subtype: a positive complex matrix "
                    + "with trace one. Matrix coordinates use its star algebra equivalence. "
                    + "No purity, invertibility, or nonzero imaginary coordinate is required.",
                DescribeRole.Definition),
            Entry("effects", "RealEffect", "The entire real effect interval",
                "An effect is a positive semidefinite complex matrix whose complement in "
                    + "the identity is positive semidefinite and whose entries have zero "
                    + "imaginary part. Positivity supplies Hermitian symmetry, so these are "
                    + "exactly the real symmetric operators between zero and the identity "
                    + "in the specified basis.", DescribeRole.Definition),
            Entry("pair-effect", "pairEffect", "A projection onto two basis vectors",
                "For distinct basis indices, take one half of the outer product of their "
                    + "sum with its conjugate. This is a real effect: the matrix and its "
                    + "complement are positive semidefinite, and its entries are real.",
                DescribeRole.Definition),
            Entry("probability", "probability", "Physical trace probabilities",
                "The probability is the real part of the trace of the effect times the state, "
                    + "with its membership in the closed unit interval proved from positivity "
                    + "and trace normalization. Positivity of this trace also gives its zero "
                    + "imaginary part.", DescribeRole.Definition),
            Entry("statistics", "SameRealStatistics", "Equality on every real effect",
                "Statistical equality quantifies over every effect in the real effect interval. "
                    + "The coordinate projectors and the normalized projectors on sums of two "
                    + "basis vectors are valid effects. Their probabilities recover all entries "
                    + "of the real symmetric part; they are separate measurement settings.",
                DescribeRole.Definition),
            Entry("conjugation", "conjugate", "The physical conjugate state",
                "On Hermitian input, transpose is entrywise complex conjugation. Transpose "
                    + "preserves positivity, trace, and rank, including on every singular stratum.",
                DescribeRole.Definition),
            Entry("basis", "CopyIndex", "Joint product-basis labels",
                "Zero copies use a singleton basis, one copy uses the original basis, and "
                    + "successive copies use Cartesian products. This construction allows an "
                    + "arbitrary finite basis type, including an empty carrier.",
                DescribeRole.Definition),
            Entry("copies", "copies", "Independent identically prepared tensor copies",
                "Each positive copy count is constructed recursively with the native "
                    + "productState Kronecker product, preserving positivity and trace one. "
                    + "The zero-copy matrix is the identity on the singleton carrier. Empty "
                    + "input carriers have no trace-one density states.", DescribeRole.Definition),
            Entry("classification", "real_copy_classification",
                "Complete classification and fixed and rank strata",
                "The theorem states the two-copy equivalence, the equivalence for all positive "
                    + "copy counts, and the equivalence for every fixed count at least two. "
                    + "The two possible states are the original state and its conjugate. They "
                    + "coincide exactly when every imaginary entry is zero. Otherwise the "
                    + "fiber has exactly two distinct states. Every state in the fiber has "
                    + "the same matrix rank. These statements include mixed and singular states "
                    + "and do not assume a geometric chart.", DescribeRole.Theorem),
            Entry("five-mode-coordinate", "fiveModeRealCoordinate",
                "Actual normalized one-copy coordinate",
                "For a Fin 5 density state this is its entrywise real Hermitian matrix in the "
                    + "specified basis. Equality of every real effect probability is proved "
                    + "equivalent to equality of these coordinates.", DescribeRole.Definition),
            Entry("five-mode-image", "fiveModePhysicalImage",
                "Actual physical statistical image",
                "The image ranges over native positive trace-one density matrices, including "
                    + "mixed, rank-deficient, and real states. It is not an assumed chart.", DescribeRole.Definition),
            Entry("five-mode-image-dimension", "five_mode_physical_image_dimension",
                "Normalized visible dimension fourteen",
                "The affine direction of the actual normalized one-copy image has finrank 14. "
                    + "The proof uses the trace-one symmetric carrier and actual positive/negative "
                    + "density perturbations, so the number is intrinsic to this image and not a "
                    + "finite-state count. The same theorem identifies equality on the entire real "
                    + "effect interval with equality of these actual coordinates.", DescribeRole.Theorem),
            Entry("five-mode-orbit-relation", "fiveModeOrbitRel",
                "Literal conjugation orbit relation",
                "The quotient identifies exactly a state with itself or with its entrywise complex "
                    + "conjugate. This is a nonlinear finite orbit identification on actual density "
                    + "states, not a linear kernel quotient.", DescribeRole.Definition),
            Entry("five-mode-orbit-quotient", "fiveModeOrbitQuotient",
                "Actual orbit quotient carrier",
                "The quotient is constructed from the density-state setoid and has a surjective "
                    + "representative projection. Every rank stratum and the real fixed stratum remain "
                    + "in its domain.", DescribeRole.Definition),
            Paragraph(Text(
                "Two-copy real entries have the form of a product of two real entries minus "
                + "a product of two imaginary entries. The actual partial trace recovers the "
                + "one-copy real matrix because the second density matrix has trace one. "
                + "Equality then fixes every product of imaginary entries. A nonzero imaginary "
                + "entry fixes one common sign for all entries; if none exists, both matrices "
                + "are real. Repeated actual partial traces reduce any larger copy count to "
                + "two copies. Conjugation commutes with the Kronecker products and preserves "
                + "all real-effect probabilities.")),
            Paragraph(Text(
                "The statement requires independent preparation and the full real joint effect "
                + "interval. A restricted single-system gate menu does not establish either "
                + "requirement. In five modes the actual normalized one-copy image has affine "
                + "dimension fourteen, and the conjugation identification acts on actual normalized density matrices. "
                + "Rank-boundary states and the real fixed stratum remain in the quotient domain.")))));

    private static DocumentBlock Entry(
        string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration),
            H(title), role == DescribeRole.Definition
                ? StatementSource.WithoutFormula()
                : StatementSource.FromAuthor(declaration == "five_mode_physical_image_dimension"
                    ? ImageDimension() : Classification()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ImageDimension()
    {
        var r = Rho;
        var s = SigmaLower;
        return Disp(Seq(
            C("finrank", C("Real"), C("direction", C("affineSpan", C("Real"),
                C("fiveModePhysicalImage")))), Eq, D(1, 4), Sp, Land, RowBreak,
            Open, Forall, Sp, r, Comma, s, InMacro, C("FiveModeState"), Comma,
                C("SameRealStatistics", r, s), Sp, Iff, Sp,
                C("fiveModeRealCoordinate", r), Eq, C("fiveModeRealCoordinate", s), Close));
    }

    private static Formula Classification()
    {
        var r = Rho;
        var s = SigmaLower;
        var k = F.Id("k");
        var orbit = Seq(Open, s, Eq, r, Sp, Lor, Sp, s, Eq, C("conjugate", r), Close);
        Formula Stat(Formula count) => C("SameRealStatistics",
            C("copies", r, count), C("copies", s, count));
        return Disp(Seq(
            Forall, Sp, F.Id("n"), InMacro, C("Type"), Comma,
            OpenBracket, C("Fintype", F.Id("n")), CloseBracket, Sp,
            OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma, RowBreak,
            Forall, Sp, r, Comma, s, InMacro, C("DensityState", F.Id("n")), Comma, RowBreak,
            Open, Stat(D(2)), Sp, Iff, Sp, orbit, Close, Sp, Land, RowBreak,
            Open, Open, Forall, Sp, k, Geq, D(1), Comma, Stat(k), Close,
                Sp, Iff, Sp, orbit, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, k, Geq, D(2), Comma, Open, Stat(k), Sp, Iff, Sp, orbit, Close,
                Close, Sp, Land, RowBreak,
            Open, C("conjugate", r), Eq, r, Sp, Iff, Sp,
                C("Im", C("stateMatrix", r)), Eq, D(0), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, k, Geq, D(2), Comma, Stat(k), Sp, Implies, Sp,
                C("rank", C("stateMatrix", s)), Eq, C("rank", C("stateMatrix", r)), Close));
    }
}
