using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class PhaseOverlapReconstructionDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/PhaseOverlapReconstruction.";

    private static Formula A(string name) => F.Id(name);
    private static Formula App(string name, params Formula[] args) =>
        Call(name, args);
    private static Formula Eqn(Formula left, Formula right) =>
        Seq(left, Sp, FormulaDsl.Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Open, left, Sp, Land, Sp, right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, A(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Open, left, Sp, Rightarrow, Sp, right, Close);
    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Multiply(Formula left, Formula right) =>
        Seq(Open, left, Sp, Cdot, Sp, right, Close);
    private static Formula Norm(Formula x) => App("norm", x);
    private static Formula Inner(Formula x, Formula y) => App("inner", x, y);
    private static Formula Unit(Formula x) => Eqn(Norm(x), D(1));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three phase-shifted pairwise distances reconstruct a complex unit-sphere overlap.",
        H("Phase overlap reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-overlap-definition"),
                DeclarationHandle.Create(Gid + "phaseOverlap"),
                H("The three-phase pairwise overlap readout"),
                StatementSource.FromAuthor(Disp(DefinitionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout combines three real squared distances with the conjugate third-root coefficients. "
                        + "It is the finite phase lift used by the reconstruction theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-overlap-inner"),
                DeclarationHandle.Create(Gid + "phaseOverlap_eq_inner"),
                H("Three pairwise phase comparisons recover the inner product"),
                StatementSource.FromAuthor(Disp(InnerFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For unit vectors, norm-square expansion turns the three distance readings into the three real Fourier coefficients of the complex inner product.")),
                    Paragraph(Text(
                        "The result is conditional on the stated complex normed inner-product structure and unit norms. It introduces no measurement menu or physical probability law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-overlap-born-bound"),
                DeclarationHandle.Create(Gid + "phaseOverlap_normSq_le_one"),
                H("The reconstructed overlap obeys the unit Born bound"),
                StatementSource.FromAuthor(Disp(BoundFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inner-product identification and Cauchy--Schwarz give the squared-modulus bound for normalized vectors. This is an overlap bound, not a complete measurement postulate."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Interpretation and limits"), Blocks(
                Paragraph(Text(
                    "The real comparison is pairwise and symmetric at the observable level. The complex orientation survives in the three phase contexts and is recovered by a discrete Fourier coefficient. If the amplitude itself were globally path-independent, this residual phase would be removable and the geometry would become flat.")),
                Paragraph(Text(
                    "The module does not provide normalization as a physical preparation, effects, probability additivity, tensor products, entanglement, state update or continuous dynamics. Those bridges remain separate obligations.")))))));

    private static Formula DefinitionFormula()
    {
        Formula x = A("x"), y = A("y"), w = A("omega");
        Formula distance(Formula phase) =>
            Seq(Open, D(2), Sp, Minus, Sp,
                App("normSq", Seq(x, Minus, Multiply(phase, y))), Close);
        Formula term0 = distance(D(1));
        Formula term1 = Seq(App("conj", w), distance(w));
        Formula term2 = Seq(App("conj", App("pow", w, D(2))),
            distance(App("pow", w, D(2))));
        return Eqn(App("phaseOverlap", x, y),
            Seq(Divide(D(1), D(3)), Sp, Open, term0, Sp, Plus, Sp, term1,
                Sp, Plus, Sp, term2, Close));
    }

    private static Formula InnerFormula()
    {
        Formula h = A("H"), x = A("x"), y = A("y");
        Formula hypotheses = And(Unit(x), Unit(y));
        Formula body = Imp(hypotheses,
            Eqn(App("phaseOverlap", x, y), Inner(x, y)));
        return All("H", App("Type", D(0)),
            All("x", h, All("y", h, body)));
    }

    private static Formula BoundFormula()
    {
        Formula h = A("H"), x = A("x"), y = A("y");
        Formula body = Imp(And(Unit(x), Unit(y)),
            Seq(App("normSq", App("phaseOverlap", x, y)), Sp, Le, Sp, D(1)));
        return All("H", App("Type", D(0)),
            All("x", h, All("y", h, body)));
    }
}
