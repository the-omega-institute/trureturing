using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class PointerBasisDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nontrivial phase damping transported by a matrix equivalence fixes precisely the matrices diagonal in those coordinates, including Hadamard coordinates.",
        H("Phase Damping in Selected Coordinates"),
        Blocks(
            Paragraph(Text(
                "Write M for the complex matrices indexed by Fin(2) in each "
                + "coordinate. For an equivalence Q from M to M, a damping "
                + "coefficient c in [0,1], and rho in M, phaseDampingInBasis "
                + "applies Q, then phaseDamping, then the inverse equivalence.")),
            new DocumentBlock.DisplayFormula(Equal(
                Call("phaseDampingInBasis", F.Id("Q"), F.Id("c"), Rho),
                Seq(F.Id("Q"), Caret, Grp(Minus, D(1)),
                    Parenthesized(Call("phaseDamping", F.Id("c"),
                        Seq(F.Id("Q"), Parenthesized(Rho))))))),
            Describe.Lean(
                DescribeId.Create("transported-damping-fixed-points"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PointerBasis.phase_damping_in_basis_fixed_iff"),
                H("Fixed points are diagonal in the chosen coordinates"),
                StatementSource.FromAuthor(TransportedFormula()),
                AssessedProvenance.FromRepo(Zurek),
                Blocks(
                    Paragraph(Text(
                        "For every equivalence Q from M to M, every "
                        + "DampingCoefficient c whose real value is not one, "
                        + "and every rho in M, phaseDampingInBasis(Q,c,rho) "
                        + "equals rho if and only if Q(rho)(i,j) = 0 whenever "
                        + "i and j in Fin(2) are distinct. The equivalence is "
                        + "not required to be linear or induced by a unitary "
                        + "basis change, and rho need not be a density matrix.")),
                    Paragraph(Text(
                        "Applying the inverse-equivalence equality reduces "
                        + "the fixed-point assertion to phaseDamping(c,Q(rho)) "
                        + "= Q(rho). The diagonal fixed-point characterization in "),
                        Ref("D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal"),
                        Text(" then proves both directions. The exclusion of "
                            + "c = 1 is essential: at that coefficient the "
                            + "transported map fixes every matrix."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The Hadamard coordinate transform is conjugation by the "
                + "normalized two-point Hadamard matrix. Its entrywise "
                + "definition is the following formula, with a,b,d,e complex:")),
            new DocumentBlock.DisplayFormula(HadamardFormula()),
            Paragraph(Text(
                "Applying this transform twice returns rho, so it defines "
                + "the equivalence hadamardCoordinateEquiv with the same "
                + "forward and inverse map. The definition fourierPhaseDamping "
                + "specializes phaseDampingInBasis to this equivalence.")),
            Describe.Lean(
                DescribeId.Create("fourier-damping-fixed-points"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PointerBasis.fourier_phase_damping_fixed_iff"),
                H("Fourier-record fixed points are Hadamard-diagonal"),
                StatementSource.FromAuthor(FourierFormula()),
                AssessedProvenance.FromRepo(Zurek),
                Blocks(
                    Paragraph(Text(
                        "For every DampingCoefficient c with real value "
                        + "different from one and every rho in M, "
                        + "fourierPhaseDamping(c,rho) = rho if and only if "
                        + "hadamardCoordinates(rho)(i,j) = 0 for all distinct "
                        + "i,j in Fin(2). This is the preceding theorem "
                        + "instantiated at the explicit Hadamard equivalence. "
                        + "Zurek's pointer-state discussion provides background; "
                        + "the fixed-point statement here concerns the "
                        + "specified transported map."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula Parameters() => Seq(
        Forall, Sp, F.Id("c"), Sp, InMacro, Sp,
        OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Esc,
        Forall, Sp, Rho, Sp, InMacro, Sp, F.Id("M"), Comma, Esc,
        F.Id("c"), Sp, Neq, Sp, D(1), Sp, Rightarrow, Sp);

    private static Formula Diagonal(Formula matrix) => Seq(
        Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Sp, InMacro, Sp,
        Call("Fin", D(2)), Comma, Esc,
        F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Rightarrow, Sp,
        matrix, Underscore, Grp(F.Id("i"), F.Id("j")), Sp, Eq, Sp, D(0));

    private static Formula TransportedFormula()
    {
        var coordinates = Seq(F.Id("Q"), Parenthesized(Rho));
        var fixedPoints = Seq(
            Equal(Call("phaseDampingInBasis", F.Id("Q"), F.Id("c"), Rho), Rho),
            Sp, Iff, Sp, Parenthesized(Diagonal(coordinates)));
        return Disp(Seq(
            Forall, Sp, F.Id("Q"), Sp, InMacro, Sp,
            Call("Equiv", F.Id("M"), F.Id("M")), Comma, Esc,
            Parameters(), Parenthesized(fixedPoints)));
    }

    private static Formula FourierFormula() => Disp(Seq(
        Parameters(), Parenthesized(Seq(
            Equal(Call("fourierPhaseDamping", F.Id("c"), Rho), Rho),
            Sp, Iff, Sp,
            Parenthesized(Diagonal(Call("hadamardCoordinates", Rho)))))));

    private static Formula Matrix(Formula a, Formula b, Formula d, Formula e) => Seq(
        Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak, d, Amp, e,
        End, Grp(F.Id("pmatrix")));

    private static Formula HadamardFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var d = F.Id("d");
        var e = F.Id("e");
        return Equal(Call("hadamardCoordinates", Matrix(a, b, d, e)),
            Seq(Frac, Grp(D(1)), Grp(D(2)), Matrix(
                Seq(a, Plus, b, Plus, d, Plus, e),
                Seq(a, Minus, b, Plus, d, Minus, e),
                Seq(a, Plus, b, Minus, d, Minus, e),
                Seq(a, Minus, b, Minus, d, Plus, e))));
    }
}
