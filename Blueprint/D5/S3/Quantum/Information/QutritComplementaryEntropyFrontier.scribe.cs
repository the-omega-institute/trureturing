using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class QutritComplementaryEntropyFrontierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/czartowski2019tradeoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementary qutrit channels with a qutrit environment have a sharp lower "
            + "boundary for their map entropies, attained by a one-parameter family "
            + "and its complementary channels.",
        H("The qutrit complementary-entropy frontier"),
        Blocks(
            Node("admissible", "Stinespring isometries", "admissible", AdmissibleFormula(),
                "The input, system and environment each have dimension three. Rows of V "
                    + "are indexed by system-environment pairs, and its columns by the "
                    + "input basis. The isometry condition is the trace-preserving "
                    + "condition in the Stinespring description of Section II."),
            Node("swap", "Exchange of system and environment", "swap", SwapFormula(),
                "Exchanging the two row indices exchanges the system and environment. "
                    + "Thus channelB applied to swap V is the complementary channel "
                    + "of channelB applied to V, as in Section II, Equations (5)-(7)."),
            Node("channel-b", "The system channel", "channelB", ChannelFormula(),
                "Section II describes a channel by an isometry followed by a partial "
                    + "trace. D5.S3.Quantum.Information.PartialTraceMutualInformation."
                    + "partialTraceRight traces out the environment, the second factor. "
                    + "The displayed definition applies to every complex matrix R."),
            Node("joint", "The joint output of the maximally mixed input", "joint", JointFormula(),
                "The input is one third of the identity matrix. Multiplication by V "
                    + "and its conjugate transpose gives the joint system-environment "
                    + "output. For an isometry this is a positive matrix of trace one."),
            Node("rho-b", "The system marginal", "rhoB", MarginalFormula("rhoB", "partialTraceRight"),
                "The right partial trace of the joint output retains the system. "
                    + "For an isometry it is the image of the maximally mixed input "
                    + "under the system channel in Proposition 1."),
            Node("rho-e", "The environment marginal", "rhoE", MarginalFormula("rhoE", "partialTraceLeft"),
                "D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft "
                    + "traces out the system. The resulting environment matrix is "
                    + "the image of the maximally mixed input under the complementary "
                    + "channel in Proposition 1."),
            Node("choi", "The normalized Choi matrix", "choi", ChoiFormula(),
                "Section II, Equations (2)-(3), arranges the images of the matrix "
                    + "units into blocks. The factor one third normalizes the Choi "
                    + "matrix to trace one for an isometry. Matrix.single supplies "
                    + "the complex matrix unit with row p.1 and column q.1; the block "
                    + "entry has row p.2 and column q.2."),
            Node("output-entropy", "Entropy of the system output", "outputEntropy", EntropyFormula("outputEntropy", "rhoB"),
                "D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy "
                    + "sums Real.negMulLog over the eigenvalues. Its displayed matrix "
                    + "argument is rhoB V; the Hermiticity proof argument obtained "
                    + "from positive semidefiniteness is not displayed. The logarithm "
                    + "is natural, and zero eigenvalues contribute zero."),
            Node("map-entropy", "Entropy of the normalized Choi matrix", "mapEntropy", EntropyFormula("mapEntropy", "choi"),
                "This is the map entropy of Section II, Equation (3). The displayed "
                    + "matrix argument of D5.S3.Quantum.Information."
                    + "PartialTraceMutualInformation.spectralEntropy is choi V; "
                    + "the Hermiticity proof argument obtained from positive "
                    + "semidefiniteness is not displayed. Proposition 1 relates this "
                    + "entropy to the complementary output on the maximally mixed input."),
            Node("entropy-three", "Entropy of three real coordinates", "entropy3", EntropyThreeFormula(),
                "The sum uses Real.negMulLog, with its continuous value zero at zero. "
                    + "For a nonnegative triple of sum one this is Shannon entropy "
                    + "in nats, and for a qutrit spectrum it is the spectral entropy."),
            Node("h", "The binary-entropy coordinate", "h", BinaryEntropyFormula(),
                "Real.binEntropy is the first coordinate of the curve in Equation (20). "
                    + "On the unit interval it is the entropy of the two probabilities "
                    + "a and 1 - a, including their zero endpoint values."),
            Node("g", "The three-coordinate entropy", "g", FrontierEntropyFormula(),
                "The second coordinate is the entropy of the probabilities "
                    + "1/3 + a, 1/3 and 1/3 - a on the interval from zero to one third. "
                    + "Each summand is the Mathlib function Real.negMulLog."),
            Node("attainer", "The attaining Stinespring family", "attainer", AttainerFormula(),
                "The two nonzero environment slices are the source's Kraus operators "
                    + "diag(1, sqrt(1 - 3a), 1) and sqrt(3a) times the matrix unit "
                    + "with row zero and column one. The third slice is zero. "
                    + "Complex.ofReal displays the real-to-complex casts of the "
                    + "square roots. The family is an isometry for 0 <= a <= 1/3."),
            Node("claim", "The entropy bound and its attainment", "claim", ClaimFormula(),
                "Conjecture 1 on page 5 gives the curve and its reflection through "
                    + "equality of the two map entropies. The statement includes both "
                    + "directions of the entropy bound and the attaining family in "
                    + "both orders. The last term of Equation (20) is read as "
                    + "-(1/3 - a) log(1/3 - a), as the source's attaining channels "
                    + "give. The parameter interval here is the closed [0, 1/3]."),
            Describe.Lean(
                DescribeId.Create("qutrit-complementary-entropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp complementary-entropy bound"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The normalized Choi matrix and the environment output have "
                            + "the same nonzero spectrum: their characteristic "
                            + "polynomials differ by a factor X^6. Zero eigenvalues "
                            + "contribute zero to Real.negMulLog, so the Choi entropy "
                            + "equals the complementary output entropy, as in "
                            + "Proposition 1.")),
                    Paragraph(Text(
                        "In eigenbases of the two output matrices, the diagonal of "
                            + "the joint output is a three-by-three spectral table. "
                            + "Its entries lie between zero and one third, its total "
                            + "is one, and its row and column sums are the two output "
                            + "spectra. A row sum r and a column sum s satisfy "
                            + "r + s <= 4/3 and r - s <= 2/3.")),
                    Paragraph(Text(
                        "Two-point spreading for Real.negMulLog bounds the entropy "
                            + "of three coordinates in an interval by the entropy at "
                            + "the extreme triple. An output entropy at most h(a) "
                            + "forces a spectral coordinate r above one half, with "
                            + "u = 1 - r between zero and a. The table inequalities "
                            + "place every coordinate of the other spectrum between "
                            + "1/3 - u and 1/3 + u. Its entropy is therefore at least "
                            + "g(u), which is at least g(a) because g decreases on "
                            + "the parameter interval.")),
                    Paragraph(Text(
                        "The attaining family has system spectrum "
                            + "(1/3 + a, 1/3 - a, 1/3) and environment spectrum "
                            + "(1 - a, a, 0). These give map entropies h(a) and g(a); "
                            + "exchanging the factors gives the reflected point. "
                            + "Thus the entropy bounds are attained throughout the "
                            + "closed parameter interval."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("czartowski-braun-zyczkowski-2019-qutrit-complementary-entropy-frontier"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("qutrit-complementary-entropy-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "QutritComplementaryEntropyFrontier", name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula RealType() => Seq(Mathbb, Grp(X("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinThree() => At(Qualified("Fin"), D(3));
    private static Formula ProductType(Formula left, Formula right) =>
        Parenthesized(Seq(left, Times, right));
    private static Formula RowType() => ProductType(FinThree(), FinThree());
    private static Formula MatrixType(Formula rows, Formula columns) =>
        At(Qualified("Matrix"), rows, columns, ComplexType());
    private static Formula IsometryType() => MatrixType(RowType(), FinThree());
    private static Formula InputMatrixType() => MatrixType(FinThree(), FinThree());
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Typed(X(name), type), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Adjoint(Formula matrix) => At(Qualified("Matrix", "conjTranspose"), matrix);
    private static Formula Smul(Formula scalar, Formula value) => At(Qualified("SMul", "smul"), scalar, value);
    private static Formula Third() => Typed(new Formula.Fraction(D(1), D(3)), RealType());
    private static Formula Pair(Formula first, Formula second) => Parenthesized(Seq(first, Comma, second));
    private static Formula Projection(Formula pair, int index) => Seq(pair, Dot, new Formula.Number(index));
    private static Formula PartialTrace(string name, Formula matrix) => At(Qualified(
        "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", name), matrix);
    private static Formula SpectralEntropy(Formula matrix) => At(Qualified(
        "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "spectralEntropy"), matrix);
    private static Formula NegMulLog(Formula value) => At(Qualified("Real", "negMulLog"), value);
    private static Formula ParameterInterval() => At(Qualified("Set", "Icc"), D(0), Third());

    private static Formula AdmissibleFormula() => All("V", IsometryType(),
        Iff(LocalCall("admissible", X("V")),
            Equal(Multiply(Adjoint(X("V")), X("V")), Typed(D(1), InputMatrixType()))));

    private static Formula SwapFormula() => All("V", IsometryType(),
        Equal(LocalCall("swap", X("V")), Parenthesized(Lambda("p", RowType(),
            Lambda("i", FinThree(), At(X("V"),
                Pair(Projection(X("p"), 2), Projection(X("p"), 1)), X("i")))))));

    private static Formula ChannelFormula() => All("V", IsometryType(), All("R", InputMatrixType(),
        Equal(LocalCall("channelB", X("V"), X("R")), PartialTrace("partialTraceRight",
            Multiply(Multiply(X("V"), X("R")), Adjoint(X("V")))))));

    private static Formula JointFormula() => All("V", IsometryType(),
        Equal(LocalCall("joint", X("V")), Multiply(Multiply(X("V"),
            Smul(Third(), Typed(D(1), InputMatrixType()))), Adjoint(X("V")))));

    private static Formula MarginalFormula(string declaration, string partialTrace) => All("V", IsometryType(),
        Equal(LocalCall(declaration, X("V")), PartialTrace(partialTrace, LocalCall("joint", X("V")))));

    private static Formula ChoiFormula()
    {
        var unit = At(Qualified("Matrix", "single"), Projection(X("p"), 1),
            Projection(X("q"), 1), Typed(D(1), ComplexType()));
        var entry = At(LocalCall("channelB", X("V"), unit), Projection(X("p"), 2), Projection(X("q"), 2));
        return All("V", IsometryType(), Equal(LocalCall("choi", X("V")),
            Parenthesized(Lambda("p", RowType(), Lambda("q", RowType(), Smul(Third(), entry))))));
    }

    private static Formula EntropyFormula(string declaration, string matrix) => All("V", IsometryType(),
        Equal(LocalCall(declaration, X("V")), SpectralEntropy(LocalCall(matrix, X("V")))));

    private static Formula EntropyThreeFormula() => All("x", new Formula.TypeArrow(FinThree(), RealType()),
        Equal(LocalCall("entropy3", X("x")), Seq(
            new Formula.Subscript(Sum, Seq(X("i"), Colon, FinThree())),
            NegMulLog(At(X("x"), X("i"))))));

    private static Formula BinaryEntropyFormula() => All("a", RealType(),
        Equal(LocalCall("h", X("a")), At(Qualified("Real", "binEntropy"), X("a"))));

    private static Formula FrontierEntropyFormula() => All("a", RealType(),
        Equal(LocalCall("g", X("a")), Add(Add(NegMulLog(Add(Third(), X("a"))),
            NegMulLog(Third())), NegMulLog(Subtract(Third(), X("a"))))));

    private static Formula AttainerFormula()
    {
        Formula Single(int system, int environment, int input, Formula value) => At(Qualified("Matrix", "single"),
            Pair(new Formula.Number(system), new Formula.Number(environment)), new Formula.Number(input), value);
        Formula SquareRoot(Formula value) => At(Qualified("Complex", "ofReal"), At(Qualified("Real", "sqrt"), value));
        var first = Single(0, 0, 0, Typed(D(1), ComplexType()));
        var second = Single(1, 0, 1, SquareRoot(Subtract(D(1), Multiply(D(3), X("a")))));
        var third = Single(0, 1, 1, SquareRoot(Multiply(D(3), X("a"))));
        var fourth = Single(2, 0, 2, Typed(D(1), ComplexType()));
        return All("a", RealType(), Equal(LocalCall("attainer", X("a")), Add(Add(Add(first, second), third), fourth)));
    }

    private static Formula ClaimFormula()
    {
        var a = X("a");
        var v = X("V");
        var swapped = LocalCall("swap", v);
        var h = LocalCall("h", a);
        var g = LocalCall("g", a);
        var bounds = All("V", IsometryType(), Implies(LocalCall("admissible", v),
            All("a", RealType(), Implies(Mem(a, ParameterInterval()), And(
                Implies(Le(LocalCall("mapEntropy", v), h), Le(g, LocalCall("mapEntropy", swapped))),
                Implies(Le(LocalCall("mapEntropy", swapped), h), Le(g, LocalCall("mapEntropy", v))))))));
        var attainer = LocalCall("attainer", a);
        var complement = LocalCall("swap", attainer);
        var attained = And(LocalCall("admissible", attainer), And(
            Equal(LocalCall("mapEntropy", attainer), h), Equal(LocalCall("mapEntropy", complement), g)));
        var reflected = And(LocalCall("admissible", complement), And(
            Equal(LocalCall("mapEntropy", complement), g),
            Equal(LocalCall("mapEntropy", LocalCall("swap", complement)), h)));
        var sharpness = All("a", RealType(), Implies(Mem(a, ParameterInterval()), And(attained, reflected)));
        return Iff(Local("claim"), And(bounds, sharpness));
    }
}
