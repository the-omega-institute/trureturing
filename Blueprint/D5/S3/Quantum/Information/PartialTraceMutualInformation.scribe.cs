using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PartialTraceMutualInformationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/PartialTraceMutualInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial traces give density-state marginals, and independent product states have "
            + "zero quantum mutual information.",
        H("Partial Trace and Quantum Mutual Information"),
        Blocks(
            Paragraph(Text(
                "Application: commuting terminal menus on a common two-qubit source. "
                + "Let A = M = C squared, let rho be any positive semidefinite trace-one "
                + "matrix on A tensor M, and let E(c,b) be a finite calibrated menu. "
                + "Every effect and its identity complement are positive semidefinite, "
                + "each setting sums to the identity, and every two effects commute, "
                + "including effects from different settings. The same rho is fixed "
                + "before all setting and outcome quantifiers. The record is the entire "
                + "unnormalized matrix partialTraceRight((I tensor E(c,b)) rho).")),
            Paragraph(Text(
                "Flatten the menu using its dependent setting-outcome index. "
                + "Matrix.commute_euclideanLin and the pinned Mathlib joint-eigenspace "
                + "decomposition for a pairwise commuting symmetric family supply a "
                + "common orthonormal eigenbasis b(j). Restricting to nonzero joint "
                + "eigenspaces gives a finite independent family; its subordinate "
                + "orthonormal basis has two vectors. Thus the common basis is derived "
                + "from the actual effects. Scalar menus and an empty setting carrier "
                + "require no nontrivial-effect assumption.")),
            Paragraph(Text(
                "Put P(j) = b(j) b(j) adjoint and define the rectangular inclusion "
                + "R(j)((a,m),a') = delta(a,a') b(j)(m). The actual blocks are "
                + "D(j) = R(j) adjoint rho R(j), and K(j) = I tensor P(j) = "
                + "R(j) R(j) adjoint. Positivity under compression gives D(j) positive "
                + "semidefinite. Orthonormality gives P(j) squared = P(j), trace(P(j)) "
                + "= 1, and sum P(j) = I. Finite matrix algebra gives the same matrix "
                + "omega = sum K(j) rho K(j) = sum D(j) tensor P(j). Cyclicity of "
                + "trace and sum K(j) = I give sum trace(D(j)) = trace(rho) = 1. "
                + "Consequently omega is positive semidefinite and has trace one.")),
            Paragraph(Text(
                "This is normalized finite convex separability, including zero blocks. "
                + "Take the real weight p(j) = Re trace(D(j)). Positivity makes it "
                + "nonnegative and makes the trace real. If p(j) is positive, take "
                + "alpha(j) = D(j)/p(j); if p(j) is zero, the positive-semidefinite "
                + "zero-trace criterion gives D(j) = 0, and alpha(j) can be the fixed "
                + "density diag(1,0). In both cases D(j) = p(j) alpha(j), with "
                + "alpha(j) positive semidefinite of trace one. With beta(j) = P(j), "
                + "omega is the sum of p(j) alpha(j) tensor beta(j), and sum p(j) = 1. "
                + "No division by a zero trace or removal of a zero outcome is used.")),
            Paragraph(Text(
                "Each actual effect commutes with every P(j). For every path matrix O, "
                + "Kronecker multiplication, cyclicity of trace, idempotence of K(j), "
                + "and sum K(j) = I give trace((O tensor E(c,b)) omega) = "
                + "trace((O tensor E(c,b)) rho). The trace_mul_kron_one_right supplier "
                + "identifies these with pairings against the corresponding partial "
                + "traces. Matrix.ext_iff_trace_mul_left then gives equality of the "
                + "full conditional matrices simultaneously for all settings and outcomes, "
                + "including their probabilities and populations. Taking the identity "
                + "effect preserves the reduced path state; menu completeness makes "
                + "each sum of conditional matrices equal to that same reduced state.")),
            Paragraph(Text(
                "The application uses existing joint-basis, positive-matrix, trace and "
                + "partial-trace results; it introduces no new mathematical declaration. "
                + "For a retained history, apply the construction separately to its "
                + "supplied normalized common conditional source, independent of setting. "
                + "Calibration, conditional tomography, the two-qubit dimension and "
                + "common-source conditions are premises. The conclusion compares "
                + "terminal records and asserts neither a physical preparation procedure "
                + "nor preservation under unperformed coherent reuse. It supplies the "
                + "commuting forward implication only; the converse and Bell-record "
                + "uniqueness require their separate arguments.")),
            Describe.Lean(
                DescribeId.Create("density-positive"),
                DeclarationHandle.Create(Module + "density_posSemidef"),
                H("Density states are positive in matrix coordinates"),
                StatementSource.FromAuthor(DensityPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The star algebra equivalence from CStarMatrix to Matrix preserves nonnegativity, hence positive semidefiniteness."))),
                DescribeRole.Theorem),
            Result("left-positive", "partialTraceLeft_posSemidef",
                "Tracing out the left factor preserves positivity",
                "For arbitrary finite carriers A and B, the reduced matrix is a finite sum "
                    + "of principal submatrices.", PositivityFormula("partialTraceLeft")),
            Result("right-positive", "partialTraceRight_posSemidef",
                "Tracing out the right factor preserves positivity",
                "The same principal-submatrix argument applies to the other factor.",
                PositivityFormula("partialTraceRight")),
            Result("left-trace", "trace_partialTraceLeft",
                "The left partial trace preserves trace",
                "For every joint matrix, summing the reduced diagonal recovers its diagonal sum.",
                TraceFormula("partialTraceLeft")),
            Result("right-trace", "trace_partialTraceRight",
                "The right partial trace preserves trace",
                "Together with positivity, trace preservation gives a normalized marginal.",
                TraceFormula("partialTraceRight")),
            Describe.Lean(
                DescribeId.Create("spectral-entropy"),
                DeclarationHandle.Create(Module + "spectralEntropy"),
                H("Spectral entropy of a Hermitian matrix"),
                StatementSource.FromAuthor(SpectralEntropyFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "For any Hermitian matrix on a finite carrier, spectralEntropy sums "
                    + "Real.negMulLog over its eigenvalues. On density matrices this is "
                    + "von Neumann entropy in nats, including singular states with "
                    + "the zero-eigenvalue contribution set to zero."))),
                DescribeRole.Definition),
            Result("charpoly-conj-unitary", "charpoly_conj_unitary",
                "Unitary conjugation preserves the characteristic polynomial",
                "For every finite matrix index type, conjugation by a matrix whose adjoint "
                    + "times the matrix is the identity leaves the characteristic polynomial unchanged.",
                CharpolyConjugacyFormula()),
            Describe.Lean(
                DescribeId.Create("mutual-information"),
                DeclarationHandle.Create(Module + "quantumMutualInformation"),
                H("Mutual information of a joint density state"),
                StatementSource.FromAuthor(MutualInformationFormula()),
                AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "The only input is the joint state. marginalRight retains A and "
                    + "marginalLeft retains B; each is constructed by partial trace."))),
                DescribeRole.Definition),
            Result("product-entropy", "vonNeumannEntropy_productState",
                "Entropy adds on independent product states",
                "The spectrum of the product is the multiset of pairwise eigenvalue products. "
                    + "For any two density states on finite carriers, including singular states, "
                    + "the proof uses the zero value of x log x at zero.", ProductEntropyFormula()),
            Result("product-information", "quantumMutualInformation_productState",
                "Independent product states have zero mutual information",
                "The actual partial traces recover the two factors. Their entropies cancel "
                    + "the entropy of the product by tensor additivity.", ProductInformationFormula()))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/blore2026partialtrace")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula DensityPositivityFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho");
        Formula body = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("PosSemidef"))),
            [new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot,
                F.Id("ofMatrix"), Dot, F.Id("symm"))), [Call("val", rho)])]);
        body = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), Call("DensityState", n), body);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, body)));
    }

    private static Formula PositivityFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("PosSemidef", F.Id("M")), Sp, Rightarrow, Sp,
        Call("PosSemidef", Call(partialTrace, F.Id("M")))));

    private static Formula TraceFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("trace", Call(partialTrace, F.Id("M"))), Sp, Eq, Sp,
        Call("trace", F.Id("M"))));

    private static Formula MutualInformationFormula() => Disp(Seq(
        Call("quantumMutualInformation", Rho), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Call("marginalRight", Rho)), Sp, Plus, Sp,
        Call("vonNeumannEntropy", Call("marginalLeft", Rho)), Sp, Minus, Sp,
        Call("vonNeumannEntropy", Rho)));

    private static Formula SpectralEntropyFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho"), h = F.Id("h"), i = F.Id("i");
        Formula matrix = Call("Matrix", n, n, Seq(Mathbb, Grp(F.Id("C"))));
        Formula hermitian = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian")));
        Formula eigenvalues = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian"), Dot, F.Id("eigenvalues")));
        Formula negMulLog = Seq(Operatorname, Grp(F.Id("Real"), Dot, F.Id("negMulLog")));
        Formula body = Seq(Call("spectralEntropy", h), Sp, Eq, Sp,
            Sum, Underscore, Grp(i, Colon, n), Sp,
            new Formula.Apply(negMulLog, [new Formula.Apply(eigenvalues, [h, i])]));
        Formula bindH = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("h"), new Formula.Apply(hermitian, [rho]), body);
        Formula bindRho = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), matrix, bindH);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, bindRho)));
    }

    private static Formula CharpolyConjugacyFormula()
    {
        Formula i = F.Id("i"), rho = F.Id("rho"), unitary = F.Id("U");
        Formula matrix = Call("Matrix", i, i, Seq(Mathbb, Grp(F.Id("C"))));
        Formula star = Call("star", unitary);
        Formula conjugate = new Formula.Binary(
            new Formula.Binary(unitary, FormulaBinaryOperator.Multiply, rho),
            FormulaBinaryOperator.Multiply, star);
        Formula hypothesis = new Formula.Relation(
            new Formula.Binary(star, FormulaBinaryOperator.Multiply, unitary),
            FormulaRelationOperator.Equal, Num(1));
        Formula conclusion = new Formula.Relation(
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("charpoly"))),
                [conjugate]), FormulaRelationOperator.Equal,
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("charpoly"))),
                [rho]));
        Formula body = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), matrix,
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("U"), matrix,
                new Formula.Logic(Seq(Open, hypothesis, Close), FormulaLogicOperator.Implies,
                    Seq(Open, conclusion, Close))));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", i), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", i), CloseBracket, Sp, body)));
    }

    private static Formula ProductEntropyFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("vonNeumannEntropy", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Rho), Sp, Plus, Sp,
        Call("vonNeumannEntropy", SigmaLower)));

    private static Formula ProductInformationFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("quantumMutualInformation", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Num(0)));
}
