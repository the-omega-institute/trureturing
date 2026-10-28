using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ConditionalHockeyStickOrthogonalReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional hockey-stick ratio sets equal their orthogonal subsets and are independent of gamma at least one.",
        H("Orthogonal reduction for conditional hockey-stick ratios"),
        Blocks(
            Paragraph(Text(
                "QuantumChannel(A,B) is the completely positive, trace-preserving map from "
                    + "A to B of FiniteStateChannel. The reference coordinate is the first "
                    + "factor of R times A. Matrix.PosSemidef means positive semidefinite, "
                    + "Matrix.trace is the complex trace, and RHLinalg.rtrace is its real "
                    + "part. The notation X+ denotes CFC.posPart(X). Anonymous brackets "
                    + "supply the displayed type-class structures; Type allows arbitrary "
                    + "universes except that the types in ratios and claim lie in Type 0.")),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-positive-block-diagonal"),
                DeclarationHandle.Create(Prefix + "posSemidef_blockDiagonal"),
                H("Positive semidefinite dependent block matrices"),
                StatementSource.FromAuthor(Disp(BlockDiagonalFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite family of finite square complex matrices, positivity "
                        + "of every block implies positivity of Matrix.blockDiagonal'. "
                        + "Each block may have its own index type, including an empty one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-partial-trace-scalar"),
                DeclarationHandle.Create(Prefix + "partialTraceRight_smul"),
                H("Scalar multiplication commutes with the right partial trace"),
                StatementSource.FromAuthor(Disp(PartialTraceScalarFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "PartialTraceMutualInformation.partialTraceRight sums the diagonal "
                        + "A coordinate and retains R. Any scalar action on C distributing "
                        + "over addition commutes with this finite sum. Neither finiteness "
                        + "of R nor decidable equality on R is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-positive-trace"),
                DeclarationHandle.Create(Prefix + "posTrace"),
                H("Trace of the positive part"),
                StatementSource.FromAuthor(Disp(SquareInputs(
                    Equal(Local("posTrace", X("X")),
                        At(Qualified("RHLinalg", "rtrace"), PositivePart(X("X"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "posTrace(X) is the real trace of the CFC positive part X+. For "
                        + "Hermitian X this is the sum of its positive eigenvalues, with "
                        + "multiplicity. The definition itself accepts every square matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-divergence"),
                DeclarationHandle.Create(Prefix + "E"),
                H("Hockey-stick divergence"),
                StatementSource.FromAuthor(Disp(FiniteTypes(["n"],
                    All("gamma", Reals(), All("rho", MatrixType(X("n")),
                        All("sigma", MatrixType(X("n")),
                            Equal(Local("E", X("gamma"), X("rho"), X("sigma")),
                                Local("posTrace", Subtract(X("rho"),
                                    Smul(X("gamma"), X("sigma"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For density matrices rho and sigma, E_gamma(rho||sigma) is "
                        + "Tr(rho - gamma sigma)+, the hockey-stick divergence of Eq. (5.1). "
                        + "The matrix definition permits every real gamma and every pair "
                        + "of square matrices; positivity and normalization enter the ratio set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-amplification"),
                DeclarationHandle.Create(Prefix + "amp"),
                H("Reference amplification of a quantum channel"),
                StatementSource.FromAuthor(Disp(FiniteTypes(["A", "B", "R"],
                    All("N", ChannelType(), All("X", JointMatrix(X("R"), X("A")),
                        Equal(Local("amp", X("N"), X("X")),
                            At(Qualified("CStarMatrix", "ofMatrix", "symm"),
                                At(Qualified("FiniteDiamondDistance", "referenceLinear"), X("N"),
                                    At(Qualified("CStarMatrix", "ofMatrix"), X("X")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "amp(N,X) is (id_R tensor N)(X). CStarMatrix.ofMatrix converts "
                        + "ordinary matrices to the C*-matrix coordinates of "
                        + "FiniteDiamondDistance.referenceLinear, and its inverse returns "
                        + "the output matrix on R times B. Every reference block is acted "
                        + "on by the same channel N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-gap"),
                DeclarationHandle.Create(Prefix + "gap"),
                H("Conditional hockey-stick gap"),
                StatementSource.FromAuthor(Disp(FiniteTypes(["R", "A"],
                    All("gamma", Reals(), All("rho", JointMatrix(X("R"), X("A")),
                        All("sigma", JointMatrix(X("R"), X("A")),
                            Equal(Local("gap", X("gamma"), X("rho"), X("sigma")),
                                Subtract(Local("E", X("gamma"), X("rho"), X("sigma")),
                                    Local("E", X("gamma"), Marginal(X("rho")),
                                        Marginal(X("sigma"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The conditional gap is E_gamma(rho||sigma) minus "
                        + "E_gamma(rho_R||sigma_R), where both reference marginals are "
                        + "taken by PartialTraceMutualInformation.partialTraceRight. "
                        + "Trace preservation makes the reference marginals of the "
                        + "amplified outputs equal the input reference marginals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-ratio-set"),
                DeclarationHandle.Create(Prefix + "ratios"),
                H("Ratios over all finite reference systems"),
                StatementSource.FromAuthor(Disp(RatiosFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The set ranges over every finite reference type R and every pair "
                        + "of positive semidefinite trace-one matrices on R times A. "
                        + "Its denominator is strictly positive as required by Remark 2; "
                        + "all quantities are finite real numbers in finite dimension. "
                        + "The choice orth=true adds rho sigma=0, giving the orthogonal "
                        + "subset; orth=false imposes no extra condition. The numerator "
                        + "is the conditional output gap, so these are the ratios in "
                        + "Eq. (2.14). The existential brackets choose the finite-type "
                        + "structures for each reference type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Orthogonal reduction and independence of the parameter"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Section 9 asks whether the hockey-stick contraction coefficient "
                        + "can be optimized over orthogonal states, extending the "
                        + "trace-distance conclusion of Proposition 8. Here the conditional "
                        + "coefficient is considered: equality holds for the full sets "
                        + "of attainable ratios, and the second conjunct strengthens "
                        + "monotonicity to independence of gamma for gamma at least one. "
                        + "Equality of the sets gives equality of their suprema, including "
                        + "the source's zero convention when no positive denominator exists."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-hockey-stick-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Orthogonal states attain exactly the same ratios"),
                StatementSource.FromAuthor(Disp(Name("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Given density matrices rho and sigma and a positive target "
                            + "parameter delta, write H = rho - gamma sigma = P - Q for "
                            + "the Jordan decomposition: P=H+, Q=(-H)+, P,Q are positive "
                            + "semidefinite and PQ=0. Put p=Tr(P), q=Tr(Q), "
                            + "c=1/(1+p+q/delta), a=1-cp and b=delta-cq. Then c>0 "
                            + "and a,b are nonnegative, with cp+a=1 and "
                            + "(c/delta)q+b/delta=1.")),
                    Paragraph(Text(
                        "Choose a pure density matrix tau on A and enlarge the reference "
                            + "to R direct-sum C direct-sum C. The two C summands are "
                            + "one-dimensional reference spaces, represented by singleton "
                            + "index types. After distributing the tensor product, set "
                            + "rho' = cP direct-sum a tau direct-sum 0 and "
                            + "sigma' = (c/delta)Q direct-sum 0 direct-sum (b/delta)tau. "
                            + "They are orthogonal density matrices, and their difference "
                            + "rho' - delta sigma' is cH direct-sum a tau "
                            + "direct-sum (-b tau).")),
                    Paragraph(Text(
                        "Positive-part traces add across the three blocks. Both the "
                            + "reference amplification and the partial trace respect the three blocks. "
                            + "Consequently the input divergence, output divergence and "
                            + "reference-marginal divergence each become c times their "
                            + "original value plus a. Subtracting the marginal term cancels "
                            + "a, so both conditional gaps are multiplied by the same "
                            + "positive c. The denominator stays positive and the ratio "
                            + "is unchanged. Taking delta=gamma yields the orthogonal "
                            + "reduction; transferring in both directions between any "
                            + "gamma,delta at least one yields parameter independence. "
                            + "Thus the conditional coefficient equals its trace-distance "
                            + "value throughout this range."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hirche-george-nuradha-wilde-2026-conditional-hockey-stick-orthogonal-reduction"),
                    ResolutionKind.Proved))
        )));

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
    private static Formula Name(string name) => Qualified(
        "D5", "S3", "Quantum", "Divergence", "ConditionalHockeyStickOrthogonalReduction", name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Local(string name, params Formula[] arguments) => At(Name(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(F.Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        for (var index = types.Length - 1; index >= 0; index--)
            body = Seq(OpenBracket, types[index], CloseBracket, Sp, body);
        return body;
    }
    private static Formula Type() => Qualified("Type");
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula MatrixType(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula JointMatrix(Formula reference, Formula input) =>
        MatrixType(Seq(reference, Sp, Times, Sp, input));
    private static Formula ChannelType() => At(Qualified("FiniteStateChannel", "QuantumChannel"), X("A"), X("B"));
    private static Formula FiniteTypes(string[] names, Formula body)
    {
        for (var index = names.Length - 1; index >= 0; index--)
        {
            var type = X(names[index]);
            body = All(names[index], Type(), Instances(body,
                At(Qualified("Fintype"), type), At(Qualified("DecidableEq"), type)));
        }
        return body;
    }
    private static Formula SquareInputs(Formula body) =>
        FiniteTypes(["n"], All("X", MatrixType(X("n")), body));
    private static Formula PositivePart(Formula matrix) => new Formula.Power(matrix, Plus);
    private static Formula Marginal(Formula matrix) =>
        At(Qualified("PartialTraceMutualInformation", "partialTraceRight"), matrix);
    private static Formula Positive(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Seq(scalar, Sp, Cdot, Sp, Parenthesized(matrix));

    private static Formula BlockDiagonalFormula()
    {
        var fiber = At(X("kappa"), X("i"));
        var block = At(X("M"), X("i"));
        var diagonal = At(Seq(Qualified("Matrix", "blockDiagonal"), Apos), X("M"));
        return FiniteTypes(["iota"],
            All("kappa", new Formula.TypeArrow(X("iota"), Type()),
                Instances(All("M", All("i", X("iota"), MatrixType(fiber)),
                    Implies(All("i", X("iota"), Positive(block)), Positive(diagonal))),
                    All("i", X("iota"), At(Qualified("Fintype"), fiber)),
                    All("i", X("iota"), At(Qualified("DecidableEq"), fiber)))));
    }

    private static Formula PartialTraceScalarFormula() =>
        All("S", Type(), All("R", Type(), All("A", Type(),
            Instances(All("c", X("S"), All("X", JointMatrix(X("R"), X("A")),
                Equal(Marginal(Smul(X("c"), X("X"))), Smul(X("c"), Marginal(X("X")))))),
                At(Qualified("DistribSMul"), X("S"), Complexes()), At(Qualified("Fintype"), X("A"))))));

    private static Formula RatiosFormula()
    {
        var inputGap = Local("gap", X("gamma"), X("rho"), X("sigma"));
        var outputGap = Local("gap", X("gamma"), Local("amp", X("N"), X("rho")),
            Local("amp", X("N"), X("sigma")));
        var conditions = And(Positive(X("rho")), And(Equal(Trace(X("rho")), D(1)),
            And(Positive(X("sigma")), And(Equal(Trace(X("sigma")), D(1)),
                And(Implies(Equal(X("orth"), Qualified("true")),
                        Equal(Multiply(X("rho"), X("sigma")), D(0))),
                    And(Lt(D(0), inputGap), Equal(X("x"), new Formula.Fraction(outputGap, inputGap))))))));
        var reference = Some("R", Type(), Instances(
            Some("rho", JointMatrix(X("R"), X("A")),
                Some("sigma", JointMatrix(X("R"), X("A")), conditions)),
            At(Qualified("Fintype"), X("R")), At(Qualified("DecidableEq"), X("R"))));
        var set = Seq(OpenBrace, Typed(X("x"), Reals()), Sp, Mid, Sp, reference, CloseBrace);
        return FiniteTypes(["A", "B"], All("N", ChannelType(), All("gamma", Reals(),
            All("orth", Qualified("Bool"), Equal(Local("ratios", X("N"), X("gamma"), X("orth")), set)))));
    }

    private static Formula ClaimFormula()
    {
        Formula Ratios(Formula parameter, bool orthogonal) =>
            Local("ratios", X("N"), parameter, Qualified(orthogonal ? "true" : "false"));
        var reduction = All("gamma", Reals(), Implies(Le(D(1), X("gamma")),
            Equal(Ratios(X("gamma"), false), Ratios(X("gamma"), true))));
        var independence = All("gamma", Reals(), All("delta", Reals(),
            Implies(Le(D(1), X("gamma")), Implies(Le(D(1), X("delta")),
                Equal(Ratios(X("gamma"), false), Ratios(X("delta"), false))))));
        return Iff(Name("claim"), FiniteTypes(["A", "B"],
            All("N", ChannelType(), And(reduction, independence))));
    }
}
