using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualQubitAttainmentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualQubitAttainment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed CPTP processor realizes a three-level Schur channel using noncommuting full-rank qubit programs with exact spectral SLD information.",
        H("Exact qubit-program attainment"),
        Blocks(
            Paragraph(Text("Write In for Fin n, Mn for complex matrices indexed by In, and Mq for matrices indexed by any finite set q. A bold 1 denotes an identity matrix, while In denotes an index set. A star denotes conjugate transpose; [A,B] means AB minus BA. Matrices are identified with CStarMatrix through ofMatrix and its inverse. DensityState is the positive trace-one CStarMatrix subtype, and matrix(s) is its underlying ordinary matrix. For a real parameter a set d = 1 minus a squared. All the following matrices, including the controls and processor, depend on this one a.")),
            Describe.Lean(DescribeId.Create("rho"), DeclarationHandle.Create(Module + "rho"),
                H("Program curve"), StatementSource.FromAuthor(RhoFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is blochMatrix with scalar coefficient one and Bloch vector (a(1-u)/sqrt(d),0,u). The definition is total for real a and u, using real square root and field division; positivity is asserted only on the interval in the theorem.")))),
            Describe.Lean(DescribeId.Create("controls"), DeclarationHandle.Create(Module + "controls"),
                H("Three controls"), StatementSource.FromAuthor(ControlsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ui abbreviates controls(a)(i). The first control is the identity, the second is sqrt(d) X plus a Z, and the third is Z, where X and Z are the usual Pauli matrices.")))),
            Describe.Lean(DescribeId.Create("controlled"), DeclarationHandle.Create(Module + "controlled"),
                H("Controlled matrix"), StatementSource.FromAuthor(ControlledFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W abbreviates controlled(a). Its row and column indices are pairs consisting of a signal index in I3 and a program index in I2.")))),
            Describe.Lean(DescribeId.Create("kraus"), DeclarationHandle.Create(Module + "kraus"),
                H("Kraus matrices"), StatementSource.FromAuthor(KrausFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Kr abbreviates kraus(a)(r). Each Kraus matrix maps the joint signal-program space to the signal space.")))),
            Paragraph(Math(ChannelMatrixFormula())),
            Paragraph(Text("In the theorem, CPTP denotes the existing QuantumChannel type: a completely positive complex linear map with trace preservation. The single existential G is fixed for every u, every signal matrix, and every finite reference dimension. For k in the natural numbers, including zero, Mk(M3) means CStarMatrix Ik Ik (CStarMatrix I3 I3 complex). The operation ampk applies G independently to every reference block; its argument is the block matrix obtained by adjoining the same program rho(u) to each signal block. Thus the reference statement ranges over every block matrix, without a positivity or normalization restriction.")),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + "result"),
                H("Fixed processor and exact information"), StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All displayed conjunctions hold for each real a with 0 < a < 1. The exact signal action and distinct-parameter commutator hold for all real parameters; the full-rank density-state and information assertions hold for u in (2a-1,1). PosDef is positive definiteness, IsUnit is matrix invertibility, and h ranges over every proof that the actual matrix rho(u) is positive semidefinite. C1 on the real line is ContDiff over the reals of order one. The derivative in spectralQFI is the real derivative of this matrix-valued curve.")))),
            Paragraph(Text("The processor is obtained from the finite Kraus channel construction. The same controls give the partial trace formula and all signal coefficients:")),
            Paragraph(Math(KrausIdentityFormula())),
            Paragraph(Text("For 0 < a < 1 and u in (2a-1,1), d, b and 1-u are positive. The curve has the following derivative D and Hermitian symmetric logarithmic derivative L. The SLD equation is verified for the actual program matrix:")),
            Paragraph(Math(SldFormula())),
            Paragraph(Text("The spectral information is the existing spectralQFI of ActualPureQubitGeometry. Here V is the eigenvector unitary supplied by the Hermitian positive-semidefinite proof h, lambda are its real eigenvalues, and B is the actual tangent matrix. Division by zero is zero, as in the underlying field; for the full-rank program every spectral denominator is positive.")),
            Paragraph(Math(SpectralFormula())),
            Paragraph(Text("The identity between spectral information and the SLD energy follows from spectral_energy in ActualPureQubitFisherRank. It applies to the displayed D and L. The resulting value is the exact cost of this explicit fixed processor and program curve.")))));

    private static Formula RhoFormula() =>
        Disp(Seq(Forall, Sp, F.Id("a"), Comma, F.Id("u"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Quad, Sp,
        F.Id("d"), Eq, D(1), Minus, F.Id("a"), Caret, D(2), Comma, Quad, Sp, Rho, Underscore, F.Id("u"), Eq, Rho,
        Open, F.Id("a"), Comma, F.Id("u"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Begin, Grp(F.Id("pmatrix")), D(1),
        Plus, F.Id("u"), Amp, Sp, F.Id("a"), Open, D(1), Minus, F.Id("u"), Close, Slash, Sqrt, Grp(F.Id("d")),
        RowBreak, F.Id("a"), Open, D(1), Minus, F.Id("u"), Close, Slash, Sqrt, Grp(F.Id("d")), Amp, D(1), Minus,
        F.Id("u"), End, Grp(F.Id("pmatrix"))));

    private static Formula ControlsFormula() =>
        Disp(Seq(Forall, Sp, F.Id("a"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Quad, Sp, Open, F.Id("U"),
        Underscore, D(0), Comma, F.Id("U"), Underscore, D(1), Comma, F.Id("U"), Underscore, D(2), Close, Eq, Left,
        Open, Mathbf, Grp(D(1)), Underscore, D(2), Comma, Begin, Grp(F.Id("pmatrix")), F.Id("a"), Amp, Sqrt,
        Grp(F.Id("d")), RowBreak, Sqrt, Grp(F.Id("d")), Amp, Minus, F.Id("a"), End, Grp(F.Id("pmatrix")), Comma,
        Begin, Grp(F.Id("pmatrix")), D(1), Amp, D(0), RowBreak, D(0), Amp, Minus, D(1), End, Grp(F.Id("pmatrix")),
        Right, Close));

    private static Formula ControlledFormula() =>
        Disp(Seq(Forall, Sp, F.Id("a"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Forall, Sp, F.Id("i"), Comma,
        F.Id("j"), InMacro, Sp, F.Id("I"), Underscore, D(3), Comma, Esc, Forall, Sp, F.Id("p"), Comma, F.Id("q"),
        InMacro, Sp, F.Id("I"), Underscore, D(2), Comma, Quad, Sp, F.Id("W"), Underscore, Grp(Open, F.Id("i"),
        Comma, F.Id("p"), Close, Comma, Open, F.Id("j"), Comma, F.Id("q"), Close), Eq, Begin, Grp(F.Id("cases")),
        Open, F.Id("U"), Underscore, F.Id("i"), Close, Underscore, Grp(F.Id("pq")), Amp, F.Id("i"), Eq, F.Id("j"),
        RowBreak, D(0), Amp, F.Id("i"), Neq, Sp, F.Id("j"), End, Grp(F.Id("cases"))));

    private static Formula KrausFormula() =>
        Disp(Seq(Forall, Sp, F.Id("a"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Forall, Sp, F.Id("r"), Comma,
        F.Id("p"), InMacro, Sp, F.Id("I"), Underscore, D(2), Comma, Esc, Forall, Sp, F.Id("i"), Comma, F.Id("j"),
        InMacro, Sp, F.Id("I"), Underscore, D(3), Comma, Quad, Sp, Open, F.Id("K"), Underscore, F.Id("r"), Close,
        Underscore, Grp(F.Id("i"), Comma, Open, F.Id("j"), Comma, F.Id("p"), Close), Eq, Begin, Grp(F.Id("cases")),
        Open, F.Id("U"), Underscore, F.Id("i"), Close, Underscore, Grp(F.Id("rp")), Amp, F.Id("i"), Eq, F.Id("j"),
        RowBreak, D(0), Amp, F.Id("i"), Neq, Sp, F.Id("j"), End, Grp(F.Id("cases"))));

    private static Formula ChannelMatrixFormula() =>
        Disp(Seq(F.Id("F"), Open, F.Id("a"), Comma, F.Id("u"), Close, Eq, Begin, Grp(F.Id("pmatrix")), D(1), Amp,
        F.Id("a"), Amp, F.Id("u"), RowBreak, F.Id("a"), Amp, D(1), Amp, F.Id("a"), RowBreak, F.Id("u"), Amp,
        F.Id("a"), Amp, D(1), End, Grp(F.Id("pmatrix")), Comma, Quad, Operatorname, Grp(F.Id("Schur")), Open, Omega,
        Comma, F.Id("F"), Close, Underscore, Grp(F.Id("ij")), Eq, Omega, Underscore, Grp(F.Id("ij")), F.Id("F"),
        Underscore, Grp(F.Id("ij")), Comma, Quad, Sp, F.Id("Y"), Eq, Begin, Grp(F.Id("pmatrix")), D(0), Amp, Minus,
        F.Id("i"), RowBreak, F.Id("i"), Amp, D(0), End, Grp(F.Id("pmatrix"))));

    private static Formula ResultFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Sp, Amp, Forall, Sp, F.Id("a"), InMacro, Mathbb, Sp, F.Id("R"), Comma,
        Quad, Sp, D(0), Lt, F.Id("a"), Lt, D(1), Longrightarrow, RowBreak, Sp, Amp, Open, Forall, Sp, F.Id("i"),
        InMacro, Sp, F.Id("I"), Underscore, D(3), Comma, Esc, F.Id("U"), Underscore, F.Id("i"), Caret, Star,
        F.Id("U"), Underscore, F.Id("i"), Eq, Mathbf, Grp(D(1)), Underscore, D(2), Close, Esc, Land, Esc, F.Id("W"),
        Caret, Star, F.Id("W"), Eq, Mathbf, Grp(D(1)), Underscore, D(6), Esc, Land, Esc, F.Id("WW"), Caret, Star,
        Eq, Mathbf, Grp(D(1)), Underscore, D(6), RowBreak, Sp, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), Comma,
        F.Id("v"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, F.Id("u"), Neq, Sp, F.Id("v"), Longrightarrow, Sp,
        OpenBracket, Rho, Underscore, F.Id("u"), Comma, Rho, Underscore, F.Id("v"), CloseBracket, Eq, Frac,
        Grp(F.Id("ia"), Open, F.Id("u"), Minus, F.Id("v"), Close), Grp(D(2), Sqrt, Grp(F.Id("d"))), F.Id("Y"), Esc,
        Land, Esc, OpenBracket, Rho, Underscore, F.Id("u"), Comma, Rho, Underscore, F.Id("v"), CloseBracket, Neq,
        D(0), Close, RowBreak, Sp, Amp, Land, Esc, Exists, Sp, F.Id("G"), InMacro, Operatorname, Grp(F.Id("CPTP")),
        Open, F.Id("M"), Underscore, Grp(F.Id("I"), Underscore, D(3), Times, Sp, F.Id("I"), Underscore, D(2)),
        Comma, F.Id("M"), Underscore, D(3), Close, Comma, RowBreak, Sp, Amp, Open, Forall, Sp, F.Id("Q"), Sp,
        InMacro, Sp, F.Id("M"), Underscore, Grp(F.Id("I"), Underscore, D(3), Times, Sp, F.Id("I"), Underscore,
        D(2)), Comma, Esc, F.Id("G"), Open, Sp, F.Id("Q"), Sp, Close, Eq, OpenBracket, Sum, Underscore,
        Grp(F.Id("r"), InMacro, Sp, F.Id("I"), Underscore, D(2)), Open, F.Id("W"), Sp, F.Id("Q"), Sp, F.Id("W"),
        Caret, Star, Close, Underscore, Grp(Open, F.Id("i"), Comma, F.Id("r"), Close, Comma, Open, F.Id("j"), Comma,
        F.Id("r"), Close), CloseBracket, Underscore, Grp(F.Id("i"), Comma, F.Id("j"), InMacro, Sp, F.Id("I"),
        Underscore, D(3)), Close, RowBreak, Sp, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Mathbb, Sp,
        F.Id("R"), Comma, Esc, Forall, Omega, InMacro, Sp, F.Id("M"), Underscore, D(3), Comma, Esc, F.Id("G"), Open,
        Operatorname, Grp(F.Id("kronecker")), Open, Omega, Comma, Rho, Underscore, F.Id("u"), Close, Close, Eq,
        Operatorname, Grp(F.Id("Schur")), Open, Omega, Comma, F.Id("F"), Open, F.Id("a"), Comma, F.Id("u"), Close,
        Close, Close, RowBreak, Sp, Amp, Land, Esc, Open, Forall, Sp, F.Id("k"), InMacro, Mathbb, Sp, F.Id("N"),
        Comma, Esc, Forall, Sp, F.Id("u"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Forall, Sp, F.Id("Q"), Sp,
        InMacro, Sp, F.Id("M"), Underscore, F.Id("k"), Open, F.Id("M"), Underscore, D(3), Close, Comma, RowBreak,
        Sp, Amp, Qquad, Sp, Operatorname, Grp(F.Id("amp")), Underscore, F.Id("k"), Open, F.Id("G"), Close, Open,
        OpenBracket, Operatorname, Grp(F.Id("kronecker")), Open, Sp, F.Id("Q"), Sp, Underscore, Grp(F.Id("rs")),
        Comma, Rho, Underscore, F.Id("u"), Close, CloseBracket, Underscore, Grp(F.Id("r"), Comma, F.Id("s"),
        InMacro, Sp, F.Id("I"), Underscore, F.Id("k")), Close, Eq, OpenBracket, Operatorname, Grp(F.Id("Schur")),
        Open, Sp, F.Id("Q"), Sp, Underscore, Grp(F.Id("rs")), Comma, F.Id("F"), Open, F.Id("a"), Comma, F.Id("u"),
        Close, Close, CloseBracket, Underscore, Grp(F.Id("r"), Comma, F.Id("s"), InMacro, Sp, F.Id("I"), Underscore,
        F.Id("k")), Close, RowBreak, Sp, Amp, Land, Esc, Rho, InMacro, Sp, F.Id("C"), Caret, D(1), Open, Mathbb, Sp,
        F.Id("R"), Comma, F.Id("M"), Underscore, D(2), Close, RowBreak, Sp, Amp, Land, Esc, Open, Forall, Sp,
        F.Id("u"), InMacro, Open, D(2), F.Id("a"), Minus, D(1), Comma, D(1), Close, Comma, Esc, Operatorname,
        Grp(F.Id("PosDef")), Open, Rho, Underscore, F.Id("u"), Close, Esc, Land, Esc, Operatorname, Grp(F.Id("tr")),
        Open, Rho, Underscore, F.Id("u"), Close, Eq, D(1), RowBreak, Sp, Amp, Qquad, Land, Esc, Operatorname,
        Grp(F.Id("det")), Rho, Underscore, F.Id("u"), Eq, Frac, Grp(Open, D(1), Minus, F.Id("u"), Close, Open, D(1),
        Plus, F.Id("u"), Minus, D(2), F.Id("a"), Caret, D(2), Close), Grp(D(4), F.Id("d")), Esc, Land, Esc,
        Operatorname, Grp(F.Id("IsUnit")), Open, Rho, Underscore, F.Id("u"), Close, RowBreak, Sp, Amp, Qquad, Land,
        Esc, Open, Exists, Sp, F.Id("s"), InMacro, Operatorname, Grp(F.Id("DensityState")), Open, F.Id("I"),
        Underscore, D(2), Close, Comma, Esc, Operatorname, Grp(F.Id("matrix")), Open, F.Id("s"), Close, Eq, Rho,
        Underscore, F.Id("u"), Close, RowBreak, Sp, Amp, Qquad, Land, Esc, Open, Forall, Sp, F.Id("h"), InMacro,
        Operatorname, Grp(F.Id("PSD")), Open, Rho, Underscore, F.Id("u"), Close, Comma, Esc, Operatorname,
        Grp(F.Id("spectralQFI")), Open, Rho, Underscore, F.Id("u"), Comma, Rho, Apos, Underscore, F.Id("u"), Comma,
        F.Id("h"), Close, Eq, Frac, Grp(F.Id("d")), Grp(Open, D(1), Minus, F.Id("u"), Close, Open, D(1), Plus,
        F.Id("u"), Minus, D(2), F.Id("a"), Caret, D(2), Close), Close, Close, Sp, End, Grp(F.Id("aligned"))));

    private static Formula SldFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, F.Id("D"), Eq, Rho, Apos, Underscore, F.Id("u"), Eq, Frac,
        Grp(D(1)), Grp(D(2)), Begin, Grp(F.Id("pmatrix")), D(1), Amp, Minus, F.Id("a"), Slash, Sqrt, Grp(F.Id("d")),
        RowBreak, Minus, F.Id("a"), Slash, Sqrt, Grp(F.Id("d")), Amp, Minus, D(1), End, Grp(F.Id("pmatrix")), Comma,
        Quad, Sp, F.Id("b"), Eq, D(1), Plus, F.Id("u"), Minus, D(2), F.Id("a"), Caret, D(2), Comma, RowBreak, Sp,
        Amp, F.Id("L"), Eq, Begin, Grp(F.Id("pmatrix")), F.Id("d"), Slash, F.Id("b"), Amp, Minus, F.Id("a"), Sqrt,
        Grp(F.Id("d")), Slash, F.Id("b"), RowBreak, Minus, F.Id("a"), Sqrt, Grp(F.Id("d")), Slash, F.Id("b"), Amp,
        F.Id("a"), Caret, D(2), Slash, F.Id("b"), Minus, D(1), Slash, Open, D(1), Minus, F.Id("u"), Close, End,
        Grp(F.Id("pmatrix")), Comma, Quad, Sp, F.Id("L"), Caret, Star, Eq, F.Id("L"), Comma, Quad, Sp, F.Id("L"),
        Rho, Underscore, F.Id("u"), Plus, Rho, Underscore, F.Id("u"), Sp, F.Id("L"), Eq, D(2), F.Id("D"), Comma,
        RowBreak, Sp, Amp, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Underscore, F.Id("u"), Comma,
        F.Id("D"), Comma, F.Id("h"), Close, Eq, Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open,
        F.Id("L"), Rho, Underscore, Grp(F.Id("u")), F.Id("L"), Close, Eq, Operatorname, Grp(F.Id("Re")),
        Operatorname, Grp(F.Id("tr")), Open, F.Id("DL"), Close, Eq, Frac, Grp(F.Id("d")), Grp(Open, D(1), Minus,
        F.Id("u"), Close, F.Id("b")), Dot, Sp, End, Grp(F.Id("aligned"))));

    private static Formula SpectralFormula() =>
        Disp(Seq(Rho, Eq, F.Id("V"), Operatorname, Grp(F.Id("diag")), Open, LambdaLower, Close, F.Id("V"), Caret,
        Star, Comma, Quad, Sp, Widehat, Sp, F.Id("B"), Eq, F.Id("V"), Caret, Star, F.Id("BV"), Comma, Quad,
        Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Comma, F.Id("B"), Comma, F.Id("h"), Close, Eq, Sum,
        Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("I"), Underscore, F.Id("n")), Sum, Underscore, Grp(F.Id("j"),
        InMacro, Sp, F.Id("I"), Underscore, F.Id("n")), Frac, Grp(D(2), Bar, Widehat, Sp, F.Id("B"), Underscore,
        Grp(F.Id("ij")), Bar, Caret, D(2)), Grp(LambdaLower, Underscore, F.Id("i"), Plus, LambdaLower, Underscore,
        F.Id("j"))));

    private static Formula KrausIdentityFormula() =>
        Disp(Seq(Sum, Underscore, Grp(F.Id("r"), InMacro, Sp, F.Id("I"), Underscore, D(2)), F.Id("K"), Underscore,
        F.Id("r"), Caret, Star, F.Id("K"), Underscore, F.Id("r"), Eq, Mathbf, Grp(D(1)), Underscore, D(6), Comma,
        Quad, Sp, F.Id("G"), Open, Sp, F.Id("Q"), Sp, Close, Eq, Sum, Underscore, Grp(F.Id("r"), InMacro, Sp,
        F.Id("I"), Underscore, D(2)), F.Id("K"), Underscore, F.Id("r"), Sp, F.Id("Q"), Sp, F.Id("K"), Underscore,
        F.Id("r"), Caret, Star, Comma, Quad, Sp, Forall, Sp, F.Id("i"), Comma, F.Id("j"), InMacro, Sp, F.Id("I"),
        Underscore, D(3), Comma, Esc, Operatorname, Grp(F.Id("tr")), Open, F.Id("U"), Underscore, F.Id("i"), Rho,
        Underscore, Grp(F.Id("u")), F.Id("U"), Underscore, F.Id("j"), Caret, Star, Close, Eq, F.Id("F"), Open,
        F.Id("a"), Comma, F.Id("u"), Close, Underscore, Grp(F.Id("ij"))));
}
