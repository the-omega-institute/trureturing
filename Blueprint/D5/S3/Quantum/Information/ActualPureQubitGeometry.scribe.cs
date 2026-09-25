using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.",
        H("Pure-qubit affine geometry"),
        Blocks(
            Paragraph(Text("Throughout, Jm denotes the finite index set Fin m; a subscript j denotes evaluation at j. Matrices are complex, PSD means positive semidefinite, and 1n is the identity on the indicated finite index set. C1(I) means continuously differentiable on I over the reals. Preconnected means that I cannot be separated into two nonempty relatively open sets; it does not require I to be nonempty. D2 is the canonical space of positive trace-one qubit density states, and mat recovers the underlying matrix. All unspecified scalar arguments in the definitions below are real. In radiusMap and extendedCost, w is a function from the reals to the reals; in root, upperDiag and effect it is a real scalar. Division by zero and the real square root use their total real conventions: a zero denominator gives zero and the square root of a negative number is zero.")),
            Paragraph(Text("For spectralQFI, U is the eigenvector unitary chosen for the Hermitian matrix, and the lambda entries are its eigenvalues. The positivity proof is shown after a semicolon when its quantification matters. A prime denotes the real derivative. In the rank-two statement, the orthonormal basis is indexed by Fin 3 and its coordinate isometry is denoted O with subscript B.")),
            Describe.Lean(DescribeId.Create("spectral-sld-information"),
                DeclarationHandle.Create(Module + "spectralQFI"), H("Spectral SLD information"),
                StatementSource.FromAuthor(SpectralFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The spectral expression uses the chosen Hermitian eigenbasis and assigns zero to terms with zero denominator."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guarded-real-infimum"),
                DeclarationHandle.Create(Module + "guardedInfimum"), H("Guarded real infimum"),
                StatementSource.FromAuthor(GuardedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real infimum with explicit nonempty and bounded-below guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-density-bridge"),
                DeclarationHandle.Create(Module + "densityBridge"), H("Canonical density-state bridge"),
                StatementSource.FromAuthor(DensityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bridge constructs the canonical density state represented by the given positive trace-one matrix; its subtype includes the exact recovered-matrix equality."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-program-class"),
                DeclarationHandle.Create(Module + "IsProgram"), H("Full actual program class"),
                StatementSource.FromAuthor(ProgramFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predicate quantifies the full finite measurement and pure-curve data. The interval contains the closed radius interval, and the Born equation is an equality in the complex numbers with the real affine value embedded in them. The final clause quantifies over every proof of positivity at zero, exactly as displayed, even for arbitrary real R."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-set"),
                DeclarationHandle.Create(Module + "costs"), H("Attainable actual costs"),
                StatementSource.FromAuthor(CostsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set ranges over all actual programs in the preceding class."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-infimum"),
                DeclarationHandle.Create(Module + "C2"), H("Cost infimum"),
                StatementSource.FromAuthor(CtwoFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "C2 applies the guarded infimum to the attainable cost set; when the guard fails its value is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bloch"),
                DeclarationHandle.Create(Module + "bloch"), H("Bloch vector"),
                StatementSource.FromAuthor(BlochFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three real Bloch coordinates of a two by two matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochmatrix"),
                DeclarationHandle.Create(Module + "blochMatrix"), H("Bloch matrix"),
                StatementSource.FromAuthor(BlochMatrixFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hermitian matrix with a specified real trace and Bloch vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effectreadout"),
                DeclarationHandle.Create(Module + "effectReadout"), H("Visible readout map"),
                StatementSource.FromAuthor(ReadoutFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframe"),
                DeclarationHandle.Create(Module + "reframe"), H("Orthogonal change of Bloch coordinates"),
                StatementSource.FromAuthor(ReframeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An orthogonal change of the Bloch vector preserves the trace coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochlinear"),
                DeclarationHandle.Create(Module + "blochLinear"), H("Linear Bloch map"),
                StatementSource.FromAuthor(BlochLinearFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch coordinates form a real linear map on complex matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframelinear"),
                DeclarationHandle.Create(Module + "reframeLinear"), H("Linear change of matrix coordinates"),
                StatementSource.FromAuthor(ReframeLinearFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed orthogonal Bloch frame induces a real linear map on matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root"),
                DeclarationHandle.Create(Module + "root"), H("Small quadratic root"),
                StatementSource.FromAuthor(RootFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radiusmap"),
                DeclarationHandle.Create(Module + "radiusMap"), H("Radius map"),
                StatementSource.FromAuthor(RadiusFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This real function converts an arc parameter into a radius for the effect-family statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extendedcost"),
                DeclarationHandle.Create(Module + "extendedCost"), H("Extended family cost"),
                StatementSource.FromAuthor(ExtendedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost formula extends through the zero transverse parameter for the normalization branch."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upperdiag"),
                DeclarationHandle.Create(Module + "upperDiag"), H("Upper diagonal coefficient"),
                StatementSource.FromAuthor(UpperFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complementary quadratic root determines the upper diagonal effect coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effect"),
                DeclarationHandle.Create(Module + "effect"), H("Actual effect matrix"),
                StatementSource.FromAuthor(EffectFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two diagonal coefficients and the normalized direction determine each effect matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arc"),
                DeclarationHandle.Create(Module + "arc"), H("Pure-state arc"),
                StatementSource.FromAuthor(ArcFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-rank-two-parameters"),
                DeclarationHandle.Create(Module + "actual_rank_two_parameters"), H("Actual rank-two arc and feasible coefficients"),
                StatementSource.FromAuthor(RankTwoFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The basis supplies a fixed coordinate frame. The coefficients and the signed square-root coordinate satisfy exactly the conjunction below; the last bound holds for every nonnegative radius whose closed interval lies in I.")))))));

    private static Formula SpectralFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("n"), Esc, Mathrm, Grp(F.Id("finite")), Comma, Esc, Rho, Comma, F.Id("D"),
        InMacro, Mathbb, Sp, F.Id("C"), Caret, Grp(F.Id("n"), Times, Sp, F.Id("n")), Comma, Esc, F.Id("h"), Colon, Operatorname, Grp(F.Id("PSD")), Open,
        Rho, Close, Comma, RowBreak, Amp, F.Id("U"), Eq, F.Id("U"), Underscore, F.Id("h"), Comma, Quad, Sp, F.Id("M"), Eq, F.Id("U"), Caret, Star,
        F.Id("D"), F.Id("U"), Comma, Quad, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Comma, F.Id("D"), Semi, F.Id("h"), Close, Eq, Sum,
        Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("n")), Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("n")), Frac, Grp(D(2), Bar, F.Id("M"),
        Underscore, Grp(F.Id("i"), F.Id("j")), Bar, Caret, D(2)), Grp(LambdaLower, Underscore, F.Id("i"), Plus, LambdaLower, Underscore,
        F.Id("j")), End, Grp(F.Id("aligned"))));

    private static Formula GuardedFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("S"), Subseteq, Mathbb, Sp, F.Id("R"), Comma, Quad, Operatorname,
        Grp(F.Id("guardedInfimum")), Open, F.Id("S"), Close, Eq, Begin, Grp(F.Id("cases")), Operatorname, Grp(F.Id("inf")), F.Id("S"), Amp,
        F.Id("S"), Neq, Emptyset, Esc, Land, Esc, Operatorname, Grp(F.Id("BddBelow")), Open, F.Id("S"), Close, RowBreak, D(0), Amp, Mathrm,
        Grp(F.Id("otherwise")), End, Grp(F.Id("cases")), End, Grp(F.Id("aligned"))));

    private static Formula DensityFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("M"), InMacro, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc,
        F.Id("h"), Colon, Operatorname, Grp(F.Id("PSD")), Open, F.Id("M"), Close, Comma, Esc, F.Id("h"), Underscore, F.Id("t"), Colon,
        Operatorname, Grp(F.Id("tr")), Open, F.Id("M"), Close, Eq, D(1), Comma, RowBreak, Amp, Operatorname, Grp(F.Id("densityBridge")), Open,
        F.Id("M"), Comma, F.Id("h"), Comma, F.Id("h"), Underscore, F.Id("t"), Close, InMacro, OpenBrace, F.Id("r"), InMacro, Mathcal, Sp, F.Id("D"),
        Underscore, D(2), Mid, Operatorname, Grp(F.Id("mat")), Open, F.Id("r"), Close, Eq, F.Id("M"), CloseBrace, End, Grp(F.Id("aligned"))));

    private static Formula ProgramFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("m"), InMacro, Mathbb, Sp, F.Id("N"), Comma, Esc, F.Id("p"), Comma, F.Id("v"), Colon,
        F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("R"), Comma, Esc, F.Id("R"), Comma, F.Id("Q"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc,
        F.Id("N"), Colon, F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, Rho, Colon, Mathbb, Sp,
        F.Id("R"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, F.Id("I"), Subseteq, Mathbb, Sp, F.Id("R"), Comma, RowBreak,
        Amp, Operatorname, Grp(F.Id("IsProgram")), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Comma, F.Id("N"), Comma, Rho, Comma,
        F.Id("I"), Comma, F.Id("Q"), Close, Esc, Leftrightarrow, RowBreak, Amp, Operatorname, Grp(F.Id("Open")), Open, F.Id("I"), Close, Land,
        Operatorname, Grp(F.Id("Preconnected")), Open, F.Id("I"), Close, Land, OpenBracket, Minus, F.Id("R"), Comma, F.Id("R"), CloseBracket,
        Subseteq, Sp, F.Id("I"), RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Operatorname,
        Grp(F.Id("PSD")), Open, F.Id("N"), Underscore, F.Id("j"), Close, Close, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"),
        Underscore, F.Id("m")), F.Id("N"), Underscore, F.Id("j"), Eq, D(1), Underscore, D(2), Land, Rho, InMacro, Sp, F.Id("C"), Caret, D(1), Open,
        F.Id("I"), Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Operatorname, Grp(F.Id("PSD")), Open,
        Rho, Open, F.Id("u"), Close, Close, Land, Operatorname, Grp(F.Id("tr")), Open, Rho, Open, F.Id("u"), Close, Close, Eq, D(1), Land, Rho,
        Open, F.Id("u"), Close, Caret, D(2), Eq, Rho, Open, F.Id("u"), Close, RowBreak, Amp, Qquad, Land, Exists, Sp, F.Id("r"), InMacro, Mathcal, Sp,
        F.Id("D"), Underscore, D(2), Comma, Operatorname, Grp(F.Id("mat")), Open, F.Id("r"), Close, Eq, Rho, Open, F.Id("u"), Close, Close,
        RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore,
        F.Id("m"), Comma, Operatorname, Grp(F.Id("tr")), Open, F.Id("N"), Underscore, F.Id("j"), Rho, Open, F.Id("u"), Close, Close, Eq,
        F.Id("p"), Underscore, F.Id("j"), Plus, F.Id("u"), F.Id("v"), Underscore, F.Id("j"), Land, D(0), Lt, F.Id("p"), Underscore, F.Id("j"),
        Plus, F.Id("u"), F.Id("v"), Underscore, F.Id("j"), Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("h"), Colon, Operatorname,
        Grp(F.Id("PSD")), Open, Rho, Open, D(0), Close, Close, Comma, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Open, D(0), Close,
        Comma, Rho, Apos, Open, D(0), Close, Semi, F.Id("h"), Close, Eq, F.Id("Q"), Close, End, Grp(F.Id("aligned"))));

    private static Formula CostsFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("costs")), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Eq, OpenBrace, F.Id("Q"), InMacro,
        Mathbb, Sp, F.Id("R"), Mid, Exists, Sp, F.Id("N"), Comma, Rho, Comma, F.Id("I"), Comma, Operatorname, Grp(F.Id("IsProgram")), Open, F.Id("p"),
        Comma, F.Id("v"), Comma, F.Id("R"), Comma, F.Id("N"), Comma, Rho, Comma, F.Id("I"), Comma, F.Id("Q"), Close, CloseBrace));

    private static Formula CtwoFormula() =>
        Disp(Seq(F.Id("C"), Underscore, D(2), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Eq, Operatorname,
        Grp(F.Id("guardedInfimum")), Open, Operatorname, Grp(F.Id("costs")), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Close));

    private static Formula BlochFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("bloch")), Open, F.Id("M"), Close, Eq, Open, D(2), Operatorname, Grp(F.Id("Re")), F.Id("M"), Underscore,
        Grp(D(0, 1)), Comma, Minus, D(2), Mathrm, Grp(F.Id("Im")), F.Id("M"), Underscore, Grp(D(0, 1)), Comma, Operatorname, Grp(F.Id("Re")),
        F.Id("M"), Underscore, Grp(D(0, 0)), Minus, Operatorname, Grp(F.Id("Re")), F.Id("M"), Underscore, Grp(D(1, 1)), Close, InMacro, Mathbb, Sp,
        F.Id("R"), Caret, D(3)));

    private static Formula BlochMatrixFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("blochMatrix")), Open, F.Id("a"), Comma, F.Id("r"), Close, Eq, Frac, D(1, 2), Begin,
        Grp(F.Id("pmatrix")), F.Id("a"), Plus, F.Id("r"), Underscore, D(2), Amp, F.Id("r"), Underscore, D(0), Minus, Mathrm, Grp(F.Id("i")),
        F.Id("r"), Underscore, D(1), RowBreak, Sp, F.Id("r"), Underscore, D(0), Plus, Mathrm, Grp(F.Id("i")), F.Id("r"), Underscore, D(1), Amp,
        F.Id("a"), Minus, F.Id("r"), Underscore, D(2), End, Grp(F.Id("pmatrix")), Quad, Open, F.Id("a"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc,
        F.Id("r"), InMacro, Mathbb, Sp, F.Id("R"), Caret, D(3), Close));

    private static Formula ReadoutFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("effectReadout")), Open, F.Id("N"), Close, Colon, Mathbb, Sp, F.Id("R"), Caret, D(3), To, Mathbb, Sp, F.Id("R"),
        Caret, Grp(F.Id("J"), Underscore, F.Id("m")), Comma, Quad, Operatorname, Grp(F.Id("effectReadout")), Open, F.Id("N"), Close, Open,
        F.Id("r"), Close, Underscore, F.Id("j"), Eq, Frac, Grp(Langle, Operatorname, Grp(F.Id("bloch")), Open, F.Id("N"), Underscore, F.Id("j"),
        Close, Comma, F.Id("r"), Rangle), Grp(D(2))));

    private static Formula ReframeFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("reframe")), Open, F.Id("O"), Comma, F.Id("M"), Close, Eq, Operatorname, Grp(F.Id("blochMatrix")), Open,
        Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open, F.Id("M"), Close, Comma, F.Id("O"), Open, Operatorname,
        Grp(F.Id("bloch")), Open, F.Id("M"), Close, Close, Close, Quad, Open, F.Id("O"), Colon, Mathbb, Sp, F.Id("R"), Caret, D(3), Equiv, Mathbb, Sp,
        F.Id("R"), Caret, D(3), Esc, Mathrm, Grp(F.Id("orthogonal")), Close));

    private static Formula BlochLinearFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("blochLinear")), Colon, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), To, Underscore, Grp(Mathbb, Sp,
        F.Id("R")), Mathbb, Sp, F.Id("R"), Caret, D(3), Comma, Quad, Operatorname, Grp(F.Id("blochLinear")), Open, F.Id("M"), Close, Eq,
        Operatorname, Grp(F.Id("bloch")), Open, F.Id("M"), Close));

    private static Formula ReframeLinearFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("reframeLinear")), Open, F.Id("O"), Close, Colon, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), To,
        Underscore, Grp(Mathbb, Sp, F.Id("R")), Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Quad, Operatorname,
        Grp(F.Id("reframeLinear")), Open, F.Id("O"), Close, Open, F.Id("M"), Close, Eq, Operatorname, Grp(F.Id("reframe")), Open, F.Id("O"),
        Comma, F.Id("M"), Close));

    private static Formula RootFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("root")), Open, F.Id("p"), Comma, F.Id("d"), Comma, Alpha, Comma, F.Id("e"), Comma, F.Id("w"), Close, Eq,
        Frac, Grp(D(2), Open, D(1), Minus, F.Id("e"), Close, F.Id("w"), Caret, D(2), F.Id("d"), Caret, D(2)), Grp(F.Id("p"), Minus, Alpha, Sp,
        F.Id("e"), F.Id("w"), F.Id("d"), Plus, Sqrt, Grp(Open, F.Id("p"), Minus, Alpha, Sp, F.Id("e"), F.Id("w"), F.Id("d"), Close, Caret, D(2),
        Minus, D(4), F.Id("e"), Open, D(1), Minus, F.Id("e"), Close, F.Id("w"), Caret, D(2), F.Id("d"), Caret, D(2)))));

    private static Formula RadiusFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("radiusMap")), Open, F.Id("B"), Comma, Alpha, Comma, F.Id("w"), Close, Open, F.Id("t"), Close, Eq, Frac,
        Grp(Open, D(2), F.Id("t"), Sqrt, Grp(D(1), Minus, F.Id("t"), Caret, D(2)), Minus, Bar, Alpha, Bar, F.Id("t"), Caret, D(2), Close,
        F.Id("w"), Open, F.Id("t"), Caret, D(2), Close), Grp(Open, D(1), Plus, F.Id("t"), Close, Sqrt, Sp, F.Id("B"))));

    private static Formula ExtendedFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("extendedCost")), Open, F.Id("B"), Comma, Alpha, Comma, F.Id("w"), Close, Open, F.Id("e"), Close, Eq,
        Frac, Grp(F.Id("B")), Grp(F.Id("w"), Open, F.Id("e"), Close, Caret, D(2)), Frac, Grp(D(4), Open, D(1), Minus, F.Id("e"), Close),
        Grp(D(4), Open, D(1), Minus, F.Id("e"), Close, Minus, Alpha, Caret, D(2), F.Id("e"))));

    private static Formula UpperFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("upperDiag")), Open, F.Id("p"), Comma, F.Id("d"), Comma, Alpha, Comma, F.Id("e"), Comma, F.Id("w"),
        Close, Eq, Frac, Grp(F.Id("p"), Minus, Alpha, Sp, F.Id("e"), F.Id("w"), F.Id("d"), Plus, Sqrt, Grp(Open, F.Id("p"), Minus, Alpha, Sp, F.Id("e"),
        F.Id("w"), F.Id("d"), Close, Caret, D(2), Minus, D(4), F.Id("e"), Open, D(1), Minus, F.Id("e"), Close, F.Id("w"), Caret, D(2), F.Id("d"),
        Caret, D(2))), Grp(D(2), Open, D(1), Minus, F.Id("e"), Close)));

    private static Formula EffectFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("effect")), Open, F.Id("p"), Comma, F.Id("d"), Comma, Alpha, Comma, F.Id("e"), Comma, F.Id("w"), Close,
        Eq, Begin, Grp(F.Id("pmatrix")), Operatorname, Grp(F.Id("upperDiag")), Open, F.Id("p"), Comma, F.Id("d"), Comma, Alpha, Comma, F.Id("e"),
        Comma, F.Id("w"), Close, Amp, F.Id("w"), F.Id("d"), RowBreak, Sp, F.Id("w"), F.Id("d"), Amp, Operatorname, Grp(F.Id("root")), Open,
        F.Id("p"), Comma, F.Id("d"), Comma, Alpha, Comma, F.Id("e"), Comma, F.Id("w"), Close, End, Grp(F.Id("pmatrix"))));

    private static Formula ArcFormula() =>
        Disp(Seq(Operatorname, Grp(F.Id("arc")), Open, F.Id("e"), Comma, F.Id("x"), Comma, F.Id("c"), Comma, F.Id("u"), Close, Eq, Operatorname,
        Grp(F.Id("blochMatrix")), Open, D(1), Comma, Open, F.Id("x"), Plus, F.Id("c"), F.Id("u"), Comma, Sqrt, Grp(D(4), F.Id("e"), Open, D(1),
        Minus, F.Id("e"), Close, Minus, Open, F.Id("x"), Plus, F.Id("c"), F.Id("u"), Close, Caret, D(2)), Comma, D(1), Minus, D(2), F.Id("e"),
        Close, Close));

    private static Formula RankTwoFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("m"), InMacro, Mathbb, Sp, F.Id("N"), Comma, Esc, F.Id("N"), Colon, F.Id("J"),
        Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, Rho, Colon, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp,
        F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, F.Id("p"), Comma, F.Id("v"), Colon, F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp,
        F.Id("R"), Comma, Esc, F.Id("I"), Subseteq, Mathbb, Sp, F.Id("R"), Comma, RowBreak, Amp, Operatorname, Grp(F.Id("Open")), Open, F.Id("I"),
        Close, Land, Operatorname, Grp(F.Id("Preconnected")), Open, F.Id("I"), Close, Land, D(0), InMacro, Sp, F.Id("I"), Land, Sp, F.Id("v"), Neq, D(0),
        RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Operatorname, Grp(F.Id("PSD")),
        Open, F.Id("N"), Underscore, F.Id("j"), Close, Close, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")),
        F.Id("N"), Underscore, F.Id("j"), Eq, D(1), Underscore, D(2), Land, Rho, InMacro, Sp, F.Id("C"), Caret, D(1), Open, F.Id("I"), Close,
        RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Operatorname, Grp(F.Id("PSD")), Open, Rho, Open, F.Id("u"),
        Close, Close, Land, Operatorname, Grp(F.Id("tr")), Open, Rho, Open, F.Id("u"), Close, Close, Eq, D(1), Land, Rho, Open, F.Id("u"), Close,
        Caret, D(2), Eq, Rho, Open, F.Id("u"), Close, Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma,
        Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open,
        F.Id("N"), Underscore, F.Id("j"), Rho, Open, F.Id("u"), Close, Close, Eq, F.Id("p"), Underscore, F.Id("j"), Plus, F.Id("u"), F.Id("v"),
        Underscore, F.Id("j"), Close, RowBreak, Amp, Land, Operatorname, Grp(F.Id("rank")), Underscore, Grp(Mathbb, Sp, F.Id("R")), Open,
        Operatorname, Grp(F.Id("effectReadout")), Open, F.Id("N"), Close, Close, Eq, D(2), RowBreak, Amp, Longrightarrow, Exists, Mathcal, Sp,
        F.Id("B"), Esc, Mathrm, Grp(F.Id("orthonormal"), Esc, F.Id("basis"), Esc, F.Id("of")), Esc, Mathbb, Sp, F.Id("R"), Caret, D(3), Comma, Esc,
        Exists, Sp, F.Id("x"), Comma, F.Id("c"), Comma, Varepsilon, Comma, F.Id("s"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Exists, Sp, F.Id("A"),
        Comma, F.Id("q"), Comma, F.Id("b"), Colon, F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("R"), Comma, RowBreak, Amp, D(0), Lt,
        F.Id("c"), Land, D(0), Lt, Varepsilon, Land, Varepsilon, Le, Frac, D(1, 2), Land, Open, F.Id("s"), Eq, D(1), Lor, Sp, F.Id("s"), Eq, Minus,
        D(1), Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Esc, D(0), Le, Sp,
        F.Id("q"), Underscore, F.Id("j"), Land, D(0), Le, Sp, F.Id("A"), Underscore, F.Id("j"), Land, Sp, F.Id("b"), Underscore, F.Id("j"), Caret, D(2),
        Le, Sp, F.Id("A"), Underscore, F.Id("j"), F.Id("q"), Underscore, F.Id("j"), Land, Sp, F.Id("b"), Underscore, F.Id("j"), Eq, F.Id("v"),
        Underscore, F.Id("j"), Slash, F.Id("c"), Land, Sp, F.Id("A"), Underscore, F.Id("j"), Eq, Open, F.Id("p"), Underscore, F.Id("j"), Minus,
        F.Id("b"), Underscore, F.Id("j"), F.Id("x"), Minus, Varepsilon, Sp, F.Id("q"), Underscore, F.Id("j"), Close, Slash, Open, D(1), Minus,
        Varepsilon, Close, Close, RowBreak, Amp, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("q"),
        Underscore, F.Id("j"), Eq, D(1), RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Operatorname,
        Grp(F.Id("reframe")), Open, F.Id("O"), Underscore, Grp(Mathcal, Sp, F.Id("B")), Comma, Rho, Open, F.Id("u"), Close, Close, Eq, Operatorname,
        Grp(F.Id("blochMatrix")), Open, D(1), Comma, Open, F.Id("x"), Plus, F.Id("c"), F.Id("u"), Comma, F.Id("s"), Sqrt, Grp(D(4), Varepsilon,
        Open, D(1), Minus, Varepsilon, Close, Minus, Open, F.Id("x"), Plus, F.Id("c"), F.Id("u"), Close, Caret, D(2)), Comma, D(1), Minus, D(2),
        Varepsilon, Close, Close, Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Open, F.Id("x"), Plus,
        F.Id("c"), F.Id("u"), Close, Caret, D(2), Lt, D(4), Varepsilon, Open, D(1), Minus, Varepsilon, Close, Close, RowBreak, Amp, Land, Esc,
        Open, Forall, Sp, F.Id("R"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, D(0), Le, Sp, F.Id("R"), Land, OpenBracket, Minus, F.Id("R"), Comma,
        F.Id("R"), CloseBracket, Subseteq, Sp, F.Id("I"), Longrightarrow, Bar, F.Id("x"), Bar, Plus, F.Id("c"), F.Id("R"), Lt, Sqrt, Grp(D(4),
        Varepsilon, Open, D(1), Minus, Varepsilon, Close), Close, End, Grp(F.Id("aligned"))));
}
