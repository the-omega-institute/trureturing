using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SemiNonnegativeBackflowRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/caofitzsimmonsmannpereiralaflamme2023cptphptp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A semi-nonnegative qutrit map that is not semi-positive doubles trace distance between two states in a common Kraus context.",
        H("Semi-nonnegative maps can exhibit information backflow"), Blocks(
            Paragraph(Text(
                "Matrices have complex entries and indices in Fin(d), the integers from zero through d minus one. "
                    + "LinearMap(C,M,M) denotes the complex-linear maps on the displayed matrix space M. "
                    + "The adjoint is conjugate transpose. Matrix.PosSemidef and Matrix.PosDef mean positive semidefinite "
                    + "and positive definite, respectively. A density matrix is positive semidefinite with complex trace one; "
                    + "these two conditions are written explicitly below. The bracketed Fintype assumptions supply "
                    + "finite enumerations, and every sum ranges over its entire displayed index type.")),
            Node("IsHPTP", "Hermiticity and trace preservation", HptpFormula(),
                "For a complex-linear map, Hermiticity preservation is expressed by commuting with the adjoint "
                    + "on every matrix. Trace preservation also holds on every matrix. This is the HPTP setting "
                    + "of Definitions 1 and 2 and Theorem 2."),
            Node("IsSemiPositive", "Semi-positivity", SemiPositiveFormula(),
                "Definition 1 requires a positive-definite density matrix whose image is also a positive-definite "
                    + "density matrix. Positive definiteness is equivalent to invertibility for a density matrix. "
                    + "The predicate itself imposes no Hermiticity or trace preservation on the map; those are separate hypotheses."),
            Node("IsSemiNonnegative", "Semi-nonnegativity", SemiNonnegativeFormula(),
                "Definition 2 requires a density matrix with a density image, allowing singular matrices. "
                    + "Hermiticity and trace preservation are separate hypotheses in the statement below. "
                    + "Theorem 2 characterizes this property for HPTP maps by a pair of channels with composition Psi after Phi equal to Xi."),
            Node("traceDistance", "Trace distance", TraceDistanceFormula(),
                "Trace distance is one half of the trace norm of the difference. "
                    + "The trace norm is the real part of the trace of the positive square root of the adjoint product, "
                    + "as displayed explicitly. CFC.sqrt denotes that positive matrix square root. "
                    + "This is the trace-distance meaning of information backflow in the Outlook and its cited works."),
            Node("claim", "The no-backflow conjunct", ClaimFormula(),
                "The Outlook conjectures absence of information backflow for semi-nonnegative trace-preserving maps "
                    + "that are not semi-positive, also in higher dimensions. Here the map is complex-linear and HPTP. "
                    + "The claim quantifies over every dimension, every such map, every two normalized finite Kraus families K and L, "
                    + "and every two input density matrices. The composition hypothesis says that applying Psi after the K channel "
                    + "equals the L channel on every matrix, as in Theorem 2. The conclusion compares the two trace distances "
                    + "in this common channel context. It is the no-backflow conjunct; the separate assertion about nonuniqueness "
                    + "of the intermediate map is not part of this statement."),
            Describe.Lean(
                DescribeId.Create("semi-nonnegative-backflow-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qutrit context doubles trace distance"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write a qutrit matrix as X = [[A,u],[v,c]], with A a two-by-two block. "
                            + "Set Psi(X) = [[2A - (tr A) I/2 + c I,u],[v,-c]], where I is the two-by-two identity. "
                            + "This map is complex-linear, commutes with the adjoint and preserves trace. "
                            + "It fixes diag(1/2,1/2,0), so it is semi-nonnegative. "
                            + "For a positive-definite input, c is strictly positive and the last diagonal entry of the image is -c. "
                            + "Thus no positive-definite density has a density image, and the map is not semi-positive.")),
                    Paragraph(Text(
                        "Let P = diag(1,1,0) and let E(a,b) have entry one in row a, column b and zero elsewhere, "
                            + "using indices 1,2,3 in this paragraph. Define Xi(X) = P X P + x(3,3) P/2 "
                            + "and Phi(X) = Xi(X)/2 + (tr X) P/4. "
                            + "A Kraus family for Xi is (P,E(1,3)/2,E(1,3)/2,E(2,3)/2,E(2,3)/2). "
                            + "A Kraus family for Phi is (P/2,P/2,E(1,3)/2,E(2,3)/2,E(1,1)/2,E(1,2)/2,"
                            + "E(1,3)/2,E(2,1)/2,E(2,2)/2,E(2,3)/2). "
                            + "Both families have adjoint products summing to the qutrit identity, "
                            + "and Psi(Phi(X)) = Xi(X) for every matrix X.")),
                    Paragraph(Text(
                        "Take the input states diag(5/8,1/8,1/4) and diag(1/8,5/8,1/4). "
                            + "Phi sends them to diag(5/8,3/8,0) and diag(3/8,5/8,0), whose trace distance is 1/4. "
                            + "Xi sends them to diag(3/4,1/4,0) and diag(1/4,3/4,0), whose trace distance is 1/2. "
                            + "The asserted inequality would therefore give 1/2 at most 1/4, a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cao-fitzsimmons-mann-pereira-laflamme-2023-semi-nonnegative-backflow-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("semi-nonnegative-backflow-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name)
    {
        string[] words = name.Split('.');
        Formula[] items = new Formula[words.Length * 2 - 1];
        for (int i = 0; i < words.Length; i++)
        {
            items[2 * i] = F.Id(words[i]);
            if (i + 1 < words.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Mat => Call("Matrix", Call("Fin", F.Id("d")), Call("Fin", F.Id("d")), Complexes);
    private static Formula Map => Call("LinearMap", Complexes, Mat, Mat);
    private static Formula Dimension(Formula body) => All("d", Naturals, body);
    private static Formula MapBinders(Formula body) => Dimension(All("Psi", Map, body));
    private static Formula Adjoint(Formula x) => Call("Matrix.conjTranspose", x);
    private static Formula Trace(Formula x) => Call("Matrix.trace", x);
    private static Formula Density(Formula x) => And(Call("Matrix.PosSemidef", x), Equal(Trace(x), D(1)));
    private static Formula TraceNormValue(Formula x) =>
        Call("Complex.re", Trace(Call("CFC.sqrt", Multiply(Adjoint(x), x))));
    private static Formula TraceNormNotation(Formula x) =>
        Seq(Vert, Sp, x, Vert, Underscore, Grp(D(1)));
    private static Formula SumOver(Formula r, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(r, Colon, type), Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula HptpFormula()
    {
        Formula x = F.Id("X"), image = Apply(F.Id("Psi"), x);
        return MapBinders(Iff(Call("IsHPTP", F.Id("Psi")),
            And(All("X", Mat, Equal(Apply(F.Id("Psi"), Adjoint(x)), Adjoint(image))),
                All("X", Mat, Equal(Trace(image), Trace(x))))));
    }

    private static Formula SemiPositiveFormula()
    {
        Formula rho = F.Id("rho"), image = Apply(F.Id("Psi"), rho);
        return MapBinders(Iff(Call("IsSemiPositive", F.Id("Psi")), Some("rho", Mat,
            And(Density(rho), And(Call("Matrix.PosDef", rho),
                And(Density(image), Call("Matrix.PosDef", image)))))));
    }

    private static Formula SemiNonnegativeFormula()
    {
        Formula rho = F.Id("rho");
        return MapBinders(Iff(Call("IsSemiNonnegative", F.Id("Psi")),
            Some("rho", Mat, And(Density(rho), Density(Apply(F.Id("Psi"), rho))))));
    }

    private static Formula KrausApplyFormula(Formula k, Formula indexType, Formula x)
    {
        Formula kr = Apply(k, F.Id("r"));
        return SumOver(F.Id("r"), indexType, Multiply(Multiply(kr, x), Adjoint(kr)));
    }

    private static Formula KrausChannelFormula(Formula k, Formula indexType)
    {
        Formula kr = Apply(k, F.Id("r"));
        return Equal(SumOver(F.Id("r"), indexType, Multiply(Adjoint(kr), kr)), D(1));
    }

    private static Formula TraceDistanceFormula()
    {
        Formula rho = F.Id("rho"), sigma = F.Id("sigma"), difference = Subtract(rho, sigma);
        return Dimension(All("rho", Mat, All("sigma", Mat,
            new Formula.RelationChain(FormulaRelationOperator.Equal,
                [Call("traceDistance", rho, sigma), new Formula.Fraction(TraceNormNotation(difference), D(2)),
                    new Formula.Fraction(TraceNormValue(difference), D(2))]))));
    }

    private static Formula ClaimFormula()
    {
        Formula intermediate = F.Id("Psi"), k = F.Id("K"), l = F.Id("L"), x = F.Id("X"),
            s = F.Id("sigmaOne"), t = F.Id("sigmaTwo"), iota = F.Id("iota"), kappa = F.Id("kappa");
        Formula bound = AtMost(Call("traceDistance", KrausApplyFormula(l, kappa, s), KrausApplyFormula(l, kappa, t)),
            Call("traceDistance", KrausApplyFormula(k, iota, s), KrausApplyFormula(k, iota, t)));
        Formula states = All("sigmaOne", Mat, All("sigmaTwo", Mat, Imp(Density(s), Imp(Density(t), bound))));
        Formula composition = All("X", Mat, Equal(Apply(intermediate, KrausApplyFormula(k, iota, x)), KrausApplyFormula(l, kappa, x)));
        Formula channels = All("K", new Formula.TypeArrow(F.Id("iota"), Mat),
            All("L", new Formula.TypeArrow(F.Id("kappa"), Mat),
                Imp(KrausChannelFormula(k, iota), Imp(KrausChannelFormula(l, kappa), Imp(composition, states)))));
        Formula families = All("iota", Named("Type"), All("kappa", Named("Type"),
            Seq(Instance("Fintype", F.Id("iota")), Sp, Instance("Fintype", F.Id("kappa")), Sp, channels)));
        Formula hypotheses = And(Call("IsHPTP", intermediate), And(Call("IsSemiNonnegative", intermediate),
            new Formula.Not(Parenthesized(Call("IsSemiPositive", intermediate)))));
        return Iff(Named("claim"), MapBinders(Imp(hypotheses, families)));
    }
}
