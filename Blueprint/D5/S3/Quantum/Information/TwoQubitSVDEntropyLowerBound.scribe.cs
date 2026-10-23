using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class TwoQubitSVDEntropyLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/parzygnat2023svdentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For two unit two-qubit states with nonzero reduced transition, SVD entanglement "
            + "entropy is at least the smaller input entanglement entropy.",
        H("The two-qubit SVD entanglement entropy lower bound"),
        Blocks(
            Node("reduced-transition", "The reduced transition matrix", "reducedTransition",
                ReducedTransitionFormula(),
                "The coefficient matrices A and B represent the vectors psi and phi in "
                    + "the product basis. Matrix.vecMulVec forms the outer product of "
                    + "Function.uncurry A and star (Function.uncurry B). "
                    + "D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight "
                    + "traces out the second factor, giving the unnormalized reduced "
                    + "transition Tr_B |psi><phi| of Section 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("reduced-density", "The reduced density matrix", "reducedDensity",
                ReducedDensityFormula(),
                "D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling A "
                    + "is the outer product |psi><psi|. Its right partial trace is the "
                    + "first subsystem's reduced matrix. When RHLinalg.frobSq A = 1, "
                    + "this matrix is positive semidefinite with trace one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("svd-density", "The normalized absolute value of a transition", "svdDensity",
                SVDDensityFormula(),
                "Equation (2.1) normalizes the positive square root of T conjugate-transpose "
                    + "times T by its trace. CFC.sqrt is the positive matrix square root; "
                    + "its trace is real. SMul.smul denotes multiplication of the matrix "
                    + "by the real scalar shown. For nonzero T the trace is positive, "
                    + "so the resulting matrix is positive semidefinite with trace one. "
                    + "The formula is defined for every T; at zero it gives the zero matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The lower bound for arbitrary two-qubit inputs", "claim",
                ClaimFormula(),
                "Coefficient matrices of Frobenius norm one are exactly the unit vectors "
                    + "of the tensor product of two copies of the two-dimensional complex "
                    + "Hilbert space. Section 3.3 and Equation (3.38) propose the lower bound "
                    + "by the smaller input entanglement entropy, without requiring the two "
                    + "input entropies to coincide. The source's factor 1/<phi|psi> cancels "
                    + "in the SVD density matrix, so the nonzero reduced-transition "
                    + "condition also allows orthogonal input vectors. By definition, "
                    + "the three matrices underlying the entropy proof arguments are "
                    + "reducedDensity A, reducedDensity B and "
                    + "svdDensity (reducedTransition A B). "
                    + "D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy "
                    + "uses natural logarithms and includes zero eigenvalues with zero "
                    + "contribution.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("two-qubit-svd-entropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("SVD entropy dominates the smaller input entropy"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The partial trace gives T = A B conjugate-transpose and the "
                            + "reduced input matrices rho_psi = A A conjugate-transpose "
                            + "and rho_phi = B B conjugate-transpose. The two-by-two "
                            + "adjugate identity is ||A B conjugate-transpose||_F^2 "
                            + "+ ||A adj(B)||_F^2 = ||A||_F^2 ||B||_F^2. Applying "
                            + "||C||_F^2 >= 2 |det C| to C = A adj(B), and using "
                            + "det adj(B) = det B, yields ||A B conjugate-transpose||_F^2 "
                            + "+ 2 |det A| |det B| <= 1 for the unit inputs.")),
                    Paragraph(Text(
                        "Set D = CFC.sqrt (T conjugate-transpose times T) and s = Tr D. "
                            + "Then det D = |det T| and s^2 = ||T||_F^2 + 2 |det T| <= 1. "
                            + "Since T is nonzero, s is positive. Thus Q = D/s is a density "
                            + "matrix and det Q = |det A| |det B|/s^2 >= |det A| |det B| "
                            + ">= min(|det A|^2, |det B|^2). The last two squares are "
                            + "det rho_psi and det rho_phi.")),
                    Paragraph(Text(
                        "A two-by-two density matrix has eigenvalues p and 1 - p, "
                            + "with p between one half and one. Its determinant is p(1 - p) "
                            + "and its spectral entropy is Real.binEntropy p. This entropy "
                            + "increases with the determinant. The determinant comparison "
                            + "therefore gives the asserted entropy lower bound, including "
                            + "singular input states. This proves the two-qubit inequality "
                            + "proposed in Section 3.3 and Equation (3.38)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("parzygnat-takayanagi-taki-wei-2023-two-qubit-svd-entropy-lower-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("two-qubit-svd-entropy-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
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
        "D5", "S3", "Quantum", "Information", "TwoQubitSVDEntropyLowerBound", name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula MatrixType() => At(Qualified("Matrix"),
        At(Qualified("Fin"), D(2)), At(Qualified("Fin"), D(2)),
        Seq(Mathbb, Grp(X("C"))));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula PartialTraceRight(Formula matrix) => At(Qualified(
        "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
        "partialTraceRight"), matrix);
    private static Formula PureCoupling(Formula matrix) => At(Qualified(
        "D5", "S3", "Quantum", "QuantumChannels", "QubitWassersteinCouplings",
        "pureCoupling"), matrix);
    private static Formula SpectralEntropy(Formula hermitianProof) => At(Qualified(
        "D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
        "spectralEntropy"), Parenthesized(hermitianProof));
    private static Formula ProofName(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            var words = name.Split('_');
            Formula suffix = X(words[^1]);
            for (var i = words.Length - 2; i >= 0; --i)
                suffix = Seq(X(words[i]), Underscore, Grp(suffix));
            items.Add(suffix);
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula InputHermitianProof(Formula matrix) => At(
        Qualified("Matrix", "PosSemidef", "isHermitian"), Parenthesized(At(
            ProofName("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
                "partialTraceRight_posSemidef"), Parenthesized(At(
                    ProofName("D5", "S3", "Quantum", "QuantumChannels", "QubitWassersteinCouplings",
                        "pureCoupling_psd"), matrix)))));
    private static Formula SVDHermitianProof(Formula transition)
    {
        var positive = At(ProofName("Matrix", "nonneg_iff_posSemidef", "mp"),
            Parenthesized(At(ProofName("CFC", "sqrt_nonneg"), Parenthesized(Multiply(
                At(Qualified("Matrix", "conjTranspose"), transition), transition)))));
        var realNonnegative = Seq(Parenthesized(At(
            ProofName("Complex", "nonneg_iff", "mp"), Parenthesized(At(
                ProofName("Matrix", "PosSemidef", "trace_nonneg"), Parenthesized(positive))))),
            Dot, D(1));
        var inverseNonnegative = At(ProofName("inv_nonneg", "mpr"),
            Parenthesized(realNonnegative));
        return At(Qualified("Matrix", "PosSemidef", "isHermitian"), Parenthesized(At(
            Qualified("Matrix", "PosSemidef", "smul"),
            Parenthesized(positive), Parenthesized(inverseNonnegative))));
    }
    private static Formula SVDMatrix(Formula transition)
    {
        var absolute = At(Qualified("CFC", "sqrt"), Multiply(
            At(Qualified("Matrix", "conjTranspose"), transition), transition));
        var mass = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), absolute));
        return At(Qualified("SMul", "smul"),
            new Formula.Power(Parenthesized(mass), new Formula.Negate(D(1))), absolute);
    }

    private static Formula ReducedTransitionFormula() => All("A", MatrixType(),
        All("B", MatrixType(), Equal(LocalCall("reducedTransition", X("A"), X("B")),
            PartialTraceRight(At(Qualified("Matrix", "vecMulVec"),
                At(Qualified("Function", "uncurry"), X("A")),
                At(Qualified("star"), At(Qualified("Function", "uncurry"), X("B"))))))));

    private static Formula ReducedDensityFormula() => All("A", MatrixType(),
        Equal(LocalCall("reducedDensity", X("A")), PartialTraceRight(PureCoupling(X("A")))));

    private static Formula SVDDensityFormula() => All("T", MatrixType(),
        Equal(LocalCall("svdDensity", X("T")), SVDMatrix(X("T"))));

    private static Formula ClaimFormula()
    {
        var transition = LocalCall("reducedTransition", X("A"), X("B"));
        var bound = new Formula.Relation(
            At(Qualified("min"),
                SpectralEntropy(InputHermitianProof(X("A"))),
                SpectralEntropy(InputHermitianProof(X("B")))),
            FormulaRelationOperator.LessThanOrEqual, SpectralEntropy(SVDHermitianProof(transition)));
        var statement = All("A", MatrixType(), All("B", MatrixType(),
            ImpliesFormula(Equal(At(Qualified("RHLinalg", "frobSq"), X("A")), D(1)),
                ImpliesFormula(Equal(At(Qualified("RHLinalg", "frobSq"), X("B")), D(1)),
                    ImpliesFormula(new Formula.Relation(transition,
                        FormulaRelationOperator.NotEqual, D(0)), bound)))));
        return new Formula.Logic(Parenthesized(Local("claim")), FormulaLogicOperator.Iff,
            Parenthesized(statement));
    }
}
