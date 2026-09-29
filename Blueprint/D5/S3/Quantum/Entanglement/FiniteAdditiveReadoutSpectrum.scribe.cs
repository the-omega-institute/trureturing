using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.FiniteReadoutFormula;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteAdditiveReadoutSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive readouts of one coherent source determine quotient blocks and flat marginals.",
        H("Finite Additive Readout Spectrum"),
        Blocks(
            Paragraph(Text(
                "All notation uses the Lean definitions in FiniteAdditiveReadoutBlocks: "
                + "BlockQuotient is G modulo kernelSum(alpha,beta), which is "
                + "alpha.ker sup beta.ker; actualCoefficient is the normalized source sum; "
                + "actualJoint is its outer product; actualReducedA and actualReducedB are "
                + "partialTraceRight and partialTraceLeft of that joint matrix. "
                + "leftVectors and rightVectors are the normalized block columns; "
                + "blockWeight is card(alpha.ker) times card(beta.ker) divided by card(G). "
                + "The formula names refer to those definitions, with real weights coerced "
                + "to complex scalars for matrix and vector operations, and natural "
                + "cardinalities coerced to reals in Real.log and Real.sqrt.")),
            Paragraph(Text(
                "For finite additive commutative groups G, A and B, the two additive readouts "
                + "alpha and beta have a jointly injective paired map. Every matrix here is "
                + "computed from the source sum normalized by the square root of the source "
                + "cardinality. The quotient is G modulo the sum of the readout kernels. "
                + "The positive block weight is the product of their cardinalities divided "
                + "by the source cardinality. Logarithms are natural logarithms.")),
            Describe.Lean(
                DescribeId.Create("finite-readout-eigenspaces"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_eigenspaces"),
                H("Exact eigenspaces and dimensions"),
                StatementSource.FromAuthor(F.Disp(ActualEigenspaces())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On either side, a vector has eigenvalue equal to the positive block weight exactly "
                    + "when it lies in the range of that side's block-column matrix. The zero eigenspace "
                    + "is the kernel of its conjugate transpose. The positive eigenspaces have dimension "
                    + "equal to the quotient cardinality; the zero eigenspaces have the ambient dimension "
                    + "minus that cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-flat-reductions"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions"),
                H("Ranks and flat marginal spectra"),
                StatementSource.FromAuthor(F.Disp(ActualFlatReductions())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernels intersect only at zero, their sum has the product cardinality, and "
                    + "the source cardinality is that product times the quotient cardinality. "
                    + "The block weight is the reciprocal quotient cardinality. Both actual marginals "
                    + "have trace one and rank equal to the quotient cardinality, as does the actual "
                    + "coefficient matrix. Their positive eigenvalues equal the block weight with "
                    + "that multiplicity; all remaining eigenvalues are zero. The von Neumann entropy "
                    + "of either actual marginal is the logarithm of the quotient cardinality, equal "
                    + "to the source-cardinality logarithm minus the two kernel-cardinality logarithms. "
                    + "The actual coefficient map between Euclidean spaces has the square root of the "
                    + "block weight as each positive singular value, repeated the quotient cardinality "
                    + "times, with every subsequent singular value zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-joint-state"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_joint_state"),
                H("Normalized joint pure state"),
                StatementSource.FromAuthor(F.Disp(ActualJointState())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The outer product of the actual coefficients is positive semidefinite and "
                    + "Hermitian, has trace and rank one, and is idempotent. The coefficient norm "
                    + "square is one. The sum of the actual source basis kets equals the coefficient "
                    + "vector coordinate by coordinate, and equals the sum of the products of the "
                    + "normalized block vectors scaled by the square root of the block weight."))),
                DescribeRole.Theorem))));

    private static Formula ActualEigenspaces()
    {
        Formula u = LeftMatrix;
        Formula v = RightMatrix;
        Formula x = Id("x");
        Formula y = Id("y");
        Formula eA = C("Module.End.eigenspace", C("Matrix.mulVecLin", ReducedA), Weight);
        Formula zA = C("Module.End.eigenspace", C("Matrix.mulVecLin", ReducedA), Zero);
        Formula eB = C("Module.End.eigenspace", C("Matrix.mulVecLin", ReducedB), Weight);
        Formula zB = C("Module.End.eigenspace", C("Matrix.mulVecLin", ReducedB), Zero);
        return Theorem(And(
            All("x", new Formula.TypeArrow(A, Complex),
                Iff(Eq(MulVec(ReducedA, x), Smul(Weight, x)),
                    Ex("y", new Formula.TypeArrow(Q, Complex), Eq(MulVec(u, y), x)))),
            All("x", new Formula.TypeArrow(A, Complex),
                Iff(Eq(MulVec(ReducedA, x), Zero), Eq(MulVec(Adj(u), x), Zero))),
            All("x", new Formula.TypeArrow(B, Complex),
                Iff(Eq(MulVec(ReducedB, x), Smul(Weight, x)),
                    Ex("y", new Formula.TypeArrow(Q, Complex), Eq(MulVec(v, y), x)))),
            All("x", new Formula.TypeArrow(B, Complex),
                Iff(Eq(MulVec(ReducedB, x), Zero), Eq(MulVec(Adj(v), x), Zero))),
            Eq(C("Module.finrank", Complex, eA), Card(Q)),
            Eq(C("Module.finrank", Complex, zA), Sub(Card(A), Card(Q))),
            Eq(C("Module.finrank", Complex, eB), Card(Q)),
            Eq(C("Module.finrank", Complex, zB), Sub(Card(B), Card(Q)))), paired: true);
    }

    private static Formula ActualFlatReductions()
    {
        Formula hA = Id("hA");
        Formula hB = Id("hB");
        Formula i = Id("i");
        Formula eigenA = C("Matrix.IsHermitian.eigenvalues",
            C("Matrix.PosSemidef.isHermitian", hA), i);
        Formula eigenB = C("Matrix.IsHermitian.eigenvalues",
            C("Matrix.PosSemidef.isHermitian", hB), i);
        Formula rhoA = Id("rhoA");
        Formula rhoB = Id("rhoB");
        Formula t = C("Matrix.toEuclideanLin", CoefficientMatrix);
        Formula singular(Formula index) => C("LinearMap.singularValues", t, index);
        Formula quotientCard = Card(Q);
        Formula kernelA = C("AddMonoidHom.ker", Alpha);
        Formula kernelB = C("AddMonoidHom.ker", Beta);
        Formula spectral = And(
            Eq(Weight, Inv(quotientCard)),
            Eq(C("Matrix.trace", ReducedA), One),
            Eq(C("Matrix.trace", ReducedB), One),
            Eq(C("Matrix.rank", CoefficientMatrix), quotientCard),
            Eq(C("Matrix.rank", ReducedA), quotientCard),
            Eq(C("Matrix.rank", ReducedB), quotientCard),
            Ex("hA", C("Matrix.PosSemidef", ReducedA), And(
                All("i", A, Or(Eq(eigenA, Weight), Eq(eigenA, Zero))),
                Eq(FilterCard(A, "i", Eq(eigenA, Weight)), quotientCard),
                Eq(FilterCard(A, "i", Eq(eigenA, Zero)), Sub(Card(A), quotientCard)))),
            Ex("hB", C("Matrix.PosSemidef", ReducedB), And(
                All("i", B, Or(Eq(eigenB, Weight), Eq(eigenB, Zero))),
                Eq(FilterCard(B, "i", Eq(eigenB, Weight)), quotientCard),
                Eq(FilterCard(B, "i", Eq(eigenB, Zero)), Sub(Card(B), quotientCard)))));
        Formula entropy = Ex("rhoA", C("DensityState", A),
            Ex("rhoB", C("DensityState", B), And(
                Eq(C("densityMatrix", rhoA), ReducedA),
                Eq(C("densityMatrix", rhoB), ReducedB),
                Eq(C("vonNeumannEntropy", rhoA), C("Real.log", quotientCard)),
                Eq(C("vonNeumannEntropy", rhoB), C("Real.log", quotientCard)),
                Eq(C("Real.log", quotientCard),
                    Sub(Sub(C("Real.log", Card(G)), C("Real.log", Card(kernelA))),
                        C("Real.log", Card(kernelB)))))));
        Formula singularValues = And(
            All("i", Id("Nat"),
                Eq(singular(i), C("ite", Lt(i, quotientCard),
                    C("Real.sqrt", Weight), Zero))),
            Eq(C("Finset.card", C("Finsupp.support",
                    C("LinearMap.singularValues", t))), quotientCard));
        Formula normalization = And(
            Eq(C("inf", kernelA, kernelB), C("bot", C("AddSubgroup", G))),
            Eq(NatCard(C("kernelSum", Alpha, Beta)), Mul(NatCard(kernelA), NatCard(kernelB))),
            Eq(NatCard(G), Mul(Mul(NatCard(Q), NatCard(kernelA)), NatCard(kernelB))));
        return Theorem(And(spectral, entropy, singularValues, normalization), paired: true);
    }

    private static Formula ActualJointState()
    {
        Formula joint = C("actualJoint", Alpha, Beta);
        Formula sourceKet = C("actualSourceKet", Alpha, Beta);
        Formula p = Id("p");
        Formula q = Qvar;
        Formula pair = C("Prod", A, B);
        Formula fst = C("Prod.fst", p);
        Formula snd = C("Prod.snd", p);
        Formula coefficient = Coeff(fst, snd);
        return Theorem(And(
            C("Matrix.PosSemidef", joint),
            C("Matrix.IsHermitian", joint),
            Eq(C("Matrix.trace", joint), One),
            Eq(MatMul(joint, joint), joint),
            Eq(C("Matrix.rank", joint), One),
            Eq(SumAt("p", pair, Mul(C("star", coefficient), coefficient)), One),
            Eq(sourceKet, F.Seq(F.Open, Lambda("p", pair, coefficient), F.Close)),
            Eq(sourceKet, Smul(C("Complex.ofReal", C("Real.sqrt", Weight)),
                SumAt("q", Q, Lambda("p", pair,
                    Mul(LeftVectors(fst, q), RightVectors(snd, q))))))), paired: true);
    }

    private static Formula Id(string name) => F.Id(name);
}
